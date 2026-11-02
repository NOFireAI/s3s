// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2023-2026 The s3s Authors

use crate::error::*;
use crate::utils::hex;

use s3s::auth::Credentials;
use s3s::crypto::Checksum;
use s3s::crypto::Md5;
use s3s::dto;
use s3s::dto::PartNumber;

use std::env;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::ops::Not;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use tokio::fs;
use tokio::fs::File;
use tokio::io::{AsyncReadExt, AsyncWriteExt, BufWriter};
use tokio::sync::{OwnedRwLockReadGuard, OwnedRwLockWriteGuard, RwLock};

use numeric_cast::NumericCast;
use path_absolutize::Absolutize;
use uuid::Uuid;

/// How many locks the objects share; see [`FileSystem::lock_object_write`].
const OBJECT_LOCK_STRIPES: u64 = 1024;

#[derive(Debug)]
pub struct FileSystem {
    pub(crate) root: PathBuf,
    tmp_file_counter: AtomicU64,
    object_locks: Box<[Arc<RwLock<()>>]>,
}

pub(crate) type InternalInfo = serde_json::Map<String, serde_json::Value>;

/// Stores standard object attributes alongside user metadata
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub(crate) struct ObjectAttributes {
    /// User-defined metadata (x-amz-meta-*)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub user_metadata: Option<dto::Metadata>,

    /// Standard object attributes
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content_encoding: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content_type: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content_disposition: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content_language: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cache_control: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expires: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub website_redirect_location: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub checksum_algorithm: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub checksum_type: Option<String>,
}

fn clean_old_tmp_files(root: &Path) -> std::io::Result<()> {
    let entries = match std::fs::read_dir(root) {
        Ok(entries) => Ok(entries),
        Err(ref io_err) if io_err.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(io_err) => Err(io_err),
    }?;
    for entry in entries {
        let entry = entry?;
        let file_name = entry.file_name();
        let Some(file_name) = file_name.to_str() else { continue };
        // See `FileSystem::prepare_file_write`
        if file_name.starts_with(".tmp.") && file_name.ends_with(".internal.part") {
            std::fs::remove_file(entry.path())?;
        }
    }
    Ok(())
}

pub(crate) async fn remove_file_if_exists(path: &Path) -> Result<()> {
    match fs::remove_file(path).await {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(err.into()),
    }
}

impl FileSystem {
    pub fn new(root: impl AsRef<Path>) -> Result<Self> {
        let root = env::current_dir()?.join(root).canonicalize()?;
        clean_old_tmp_files(&root)?;
        let tmp_file_counter = AtomicU64::new(0);
        let object_locks = (0..OBJECT_LOCK_STRIPES).map(|_| Arc::new(RwLock::new(()))).collect();
        Ok(Self {
            root,
            tmp_file_counter,
            object_locks,
        })
    }

    fn object_lock_index(bucket: &str, key: &str) -> usize {
        let mut hasher = DefaultHasher::new();
        bucket.hash(&mut hasher);
        key.hash(&mut hasher);
        (hasher.finish() % OBJECT_LOCK_STRIPES).numeric_cast::<usize>()
    }

    /// Locks an object for writing.
    ///
    /// An object is three files: the body, its attributes and its internal info, which holds the
    /// stored checksums and `ETag`. A write stages all three as temporary files, then checks its
    /// conditions under this lock and renames them into place with [`publish`], and a read opens
    /// the body and loads both sidecars under [`Self::lock_object_read`]. So two conditional
    /// writers cannot both pass their check, and a reader never pairs one write's body with
    /// another write's checksums. Objects share a fixed set of locks by hash: unrelated objects
    /// can contend, but the set never grows.
    pub(crate) async fn lock_object_write(&self, bucket: &str, key: &str) -> OwnedRwLockWriteGuard<()> {
        Arc::clone(&self.object_locks[Self::object_lock_index(bucket, key)])
            .write_owned()
            .await
    }

    /// Locks an object for reading; see [`Self::lock_object_write`].
    pub(crate) async fn lock_object_read(&self, bucket: &str, key: &str) -> OwnedRwLockReadGuard<()> {
        Arc::clone(&self.object_locks[Self::object_lock_index(bucket, key)])
            .read_owned()
            .await
    }

    /// Locks a copy's destination for writing and its source for reading. The two are taken in
    /// index order, so two copies in opposite directions cannot deadlock. A source that shares the
    /// destination's lock is covered by the write lock alone.
    pub(crate) async fn lock_object_copy(
        &self,
        src_bucket: &str,
        src_key: &str,
        dst_bucket: &str,
        dst_key: &str,
    ) -> (Option<OwnedRwLockReadGuard<()>>, OwnedRwLockWriteGuard<()>) {
        let src_index = Self::object_lock_index(src_bucket, src_key);
        let dst_index = Self::object_lock_index(dst_bucket, dst_key);
        let src_lock = Arc::clone(&self.object_locks[src_index]);
        let dst_lock = Arc::clone(&self.object_locks[dst_index]);
        if src_index == dst_index {
            return (None, dst_lock.write_owned().await);
        }
        if src_index < dst_index {
            let read = src_lock.read_owned().await;
            let write = dst_lock.write_owned().await;
            (Some(read), write)
        } else {
            let write = dst_lock.write_owned().await;
            let read = src_lock.read_owned().await;
            (Some(read), write)
        }
    }

    pub(crate) fn resolve_abs_path(&self, path: impl AsRef<Path>) -> Result<PathBuf> {
        Ok(path.as_ref().absolutize_virtually(&self.root)?.into_owned())
    }

    pub(crate) fn resolve_upload_part_path(&self, upload_id: Uuid, part_number: PartNumber) -> Result<PathBuf> {
        self.resolve_abs_path(format!(".upload_id-{upload_id}.part-{part_number}"))
    }

    /// resolve object path under the virtual root
    pub(crate) fn get_object_path(&self, bucket: &str, key: &str) -> Result<PathBuf> {
        let dir = Path::new(&bucket);
        let file_path = Path::new(&key);
        self.resolve_abs_path(dir.join(file_path))
    }

    /// resolve bucket path under the virtual root
    pub(crate) fn get_bucket_path(&self, bucket: &str) -> Result<PathBuf> {
        let dir = Path::new(&bucket);
        self.resolve_abs_path(dir)
    }

    /// resolve metadata path under the virtual root (custom format)
    pub(crate) fn get_metadata_path(&self, bucket: &str, key: &str, upload_id: Option<Uuid>) -> Result<PathBuf> {
        let encode = |s: &str| base64_simd::URL_SAFE_NO_PAD.encode_to_string(s);
        let u_ext = upload_id.map(|u| format!(".upload-{u}")).unwrap_or_default();
        let file_path = format!(".bucket-{}.object-{}{u_ext}.metadata.json", encode(bucket), encode(key));
        self.resolve_abs_path(file_path)
    }

    pub(crate) fn get_internal_info_path(&self, bucket: &str, key: &str) -> Result<PathBuf> {
        let encode = |s: &str| base64_simd::URL_SAFE_NO_PAD.encode_to_string(s);
        let file_path = format!(".bucket-{}.object-{}.internal.json", encode(bucket), encode(key));
        self.resolve_abs_path(file_path)
    }

    pub(crate) fn get_upload_part_info_path(&self, upload_id: Uuid, part_number: PartNumber) -> Result<PathBuf> {
        self.resolve_abs_path(format!(".upload_part_info-{upload_id}.part-{part_number}.json"))
    }

    /// load object attributes from fs (with backward compatibility)
    pub(crate) async fn load_object_attributes(
        &self,
        bucket: &str,
        key: &str,
        upload_id: Option<Uuid>,
    ) -> Result<Option<ObjectAttributes>> {
        let path = self.get_metadata_path(bucket, key, upload_id)?;
        if path.exists().not() {
            return Ok(None);
        }
        let content = fs::read(&path).await?;

        // Try to deserialize as ObjectAttributes first (new format)
        if let Ok(attrs) = serde_json::from_slice::<ObjectAttributes>(&content) {
            return Ok(Some(attrs));
        }

        // Fall back to old format (just user metadata)
        if let Ok(user_metadata) = serde_json::from_slice::<dto::Metadata>(&content) {
            return Ok(Some(ObjectAttributes {
                user_metadata: Some(user_metadata),
                ..Default::default()
            }));
        }

        Ok(None)
    }

    /// save object attributes to fs
    pub(crate) async fn save_object_attributes(
        &self,
        bucket: &str,
        key: &str,
        attrs: &ObjectAttributes,
        upload_id: Option<Uuid>,
    ) -> Result<()> {
        let path = self.get_metadata_path(bucket, key, upload_id)?;
        let content = serde_json::to_vec(attrs)?;
        let mut file_writer = self.prepare_file_write(&path).await?;
        file_writer.writer().write_all(&content).await?;
        file_writer.writer().flush().await?;
        file_writer.done().await?;
        Ok(())
    }

    /// remove metadata from fs
    pub(crate) fn delete_metadata(&self, bucket: &str, key: &str, upload_id: Option<Uuid>) -> Result<()> {
        let path = self.get_metadata_path(bucket, key, upload_id)?;
        match std::fs::remove_file(path) {
            Ok(()) => Ok(()),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
            Err(err) => Err(err.into()),
        }
    }

    pub(crate) async fn load_internal_info(&self, bucket: &str, key: &str) -> Result<Option<InternalInfo>> {
        let path = self.get_internal_info_path(bucket, key)?;
        if path.exists().not() {
            return Ok(None);
        }
        let content = fs::read(&path).await?;
        let map = serde_json::from_slice(&content)?;
        Ok(Some(map))
    }

    pub(crate) async fn load_upload_part_info(&self, upload_id: Uuid, part_number: PartNumber) -> Result<Option<InternalInfo>> {
        let path = self.get_upload_part_info_path(upload_id, part_number)?;
        if path.exists().not() {
            return Ok(None);
        }
        let content = fs::read(&path).await?;
        let map = serde_json::from_slice(&content)?;
        Ok(Some(map))
    }

    pub(crate) async fn save_upload_part_info(
        &self,
        upload_id: Uuid,
        part_number: PartNumber,
        info: &InternalInfo,
    ) -> Result<()> {
        let path = self.get_upload_part_info_path(upload_id, part_number)?;
        let content = serde_json::to_vec(info)?;
        let mut file_writer = self.prepare_file_write(&path).await?;
        file_writer.writer().write_all(&content).await?;
        file_writer.writer().flush().await?;
        file_writer.done().await?;
        Ok(())
    }

    pub(crate) async fn delete_upload_part_info(&self, upload_id: Uuid, part_number: PartNumber) -> Result<()> {
        let path = self.get_upload_part_info_path(upload_id, part_number)?;
        remove_file_if_exists(&path).await
    }

    /// get md5 sum
    pub(crate) async fn get_md5_sum(&self, bucket: &str, key: &str) -> Result<String> {
        let object_path = self.get_object_path(bucket, key)?;
        let mut file = File::open(&object_path).await?;
        let mut buf = vec![0; 65536];
        let mut md5_hash = Md5::new();
        loop {
            let nread = file.read(&mut buf).await?;
            if nread == 0 {
                break;
            }
            md5_hash.update(&buf[..nread]);
        }
        Ok(hex(md5_hash.finalize()))
    }

    fn get_upload_info_path(&self, upload_id: &Uuid) -> Result<PathBuf> {
        self.resolve_abs_path(format!(".upload-{upload_id}.json"))
    }

    pub(crate) async fn create_upload_id(&self, cred: Option<&Credentials>) -> Result<Uuid> {
        let upload_id = Uuid::new_v4();
        let upload_info_path = self.get_upload_info_path(&upload_id)?;

        let ak: Option<&str> = cred.map(|c| c.access_key.as_str());

        let content = serde_json::to_vec(&ak)?;
        let mut file_writer = self.prepare_file_write(&upload_info_path).await?;
        file_writer.writer().write_all(&content).await?;
        file_writer.writer().flush().await?;
        file_writer.done().await?;

        Ok(upload_id)
    }

    pub(crate) async fn verify_upload_id(&self, cred: Option<&Credentials>, upload_id: &Uuid) -> Result<bool> {
        let upload_info_path = self.get_upload_info_path(upload_id)?;
        if upload_info_path.exists().not() {
            return Ok(false);
        }

        let content = fs::read(&upload_info_path).await?;
        let ak: Option<String> = serde_json::from_slice(&content)?;

        Ok(ak.as_deref() == cred.map(|c| c.access_key.as_str()))
    }

    pub(crate) async fn delete_upload_id(&self, upload_id: &Uuid) -> Result<()> {
        let upload_info_path = self.get_upload_info_path(upload_id)?;
        remove_file_if_exists(&upload_info_path).await
    }

    /// Writes `content` to a temporary file to be renamed over `path` by [`publish`].
    pub(crate) async fn stage_bytes(&self, path: &Path, content: &[u8]) -> Result<Staged> {
        let mut file_writer = self.prepare_file_write(path).await?;
        file_writer.writer().write_all(content).await?;
        file_writer.stage().await
    }

    pub(crate) async fn stage_object_attributes(&self, bucket: &str, key: &str, attrs: &ObjectAttributes) -> Result<Staged> {
        let path = self.get_metadata_path(bucket, key, None)?;
        self.stage_bytes(&path, &serde_json::to_vec(attrs)?).await
    }

    pub(crate) async fn stage_internal_info(&self, bucket: &str, key: &str, info: &InternalInfo) -> Result<Staged> {
        let path = self.get_internal_info_path(bucket, key)?;
        self.stage_bytes(&path, &serde_json::to_vec(info)?).await
    }

    /// Write to the filesystem atomically.
    /// This is done by first writing to a temporary location and then moving the file.
    pub(crate) async fn prepare_file_write<'a>(&self, path: &'a Path) -> Result<FileWriter<'a>> {
        let tmp_name = format!(".tmp.{}.internal.part", self.tmp_file_counter.fetch_add(1, Ordering::SeqCst));
        let tmp_path = self.resolve_abs_path(tmp_name)?;
        let file = File::create(&tmp_path).await?;
        let writer = BufWriter::new(file);
        Ok(FileWriter {
            tmp_path,
            dest_path: path,
            writer,
            clean_tmp: true,
        })
    }
}

pub(crate) struct FileWriter<'a> {
    tmp_path: PathBuf,
    dest_path: &'a Path,
    writer: BufWriter<File>,
    clean_tmp: bool,
}

impl<'a> FileWriter<'a> {
    pub(crate) fn tmp_path(&self) -> &Path {
        &self.tmp_path
    }

    pub(crate) fn dest_path(&self) -> &'a Path {
        self.dest_path
    }

    pub(crate) fn writer(&mut self) -> &mut BufWriter<File> {
        &mut self.writer
    }

    pub(crate) async fn done(mut self) -> Result<()> {
        if let Some(final_dir_path) = self.dest_path().parent() {
            fs::create_dir_all(&final_dir_path).await?;
        }

        fs::rename(&self.tmp_path, self.dest_path()).await?;
        self.clean_tmp = false;
        Ok(())
    }

    /// Flushes the temporary file and hands it to [`publish`] instead of renaming it now.
    pub(crate) async fn stage(mut self) -> Result<Staged> {
        self.writer.flush().await?;
        self.clean_tmp = false;
        Ok(Staged {
            tmp_path: std::mem::take(&mut self.tmp_path),
            dest_path: self.dest_path.to_owned(),
        })
    }
}

/// A flushed temporary file waiting to be renamed over its destination by [`publish`]. Dropped
/// unpublished, it removes the temporary file.
pub(crate) struct Staged {
    tmp_path: PathBuf,
    dest_path: PathBuf,
}

impl Drop for Staged {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.tmp_path);
    }
}

/// Renames each staged file over its destination, in order, while `guard` is held.
///
/// The renames run in one blocking task that owns the guard, so once they start they all run
/// with the lock held, even if the request that started them is dropped: a cancelled write cannot
/// leave a body beside the previous write's sidecars, and no reader sees the files half
/// published. The data was written and flushed when it was staged, so a full disk fails the
/// write before anything is published.
pub(crate) async fn publish<G: Send + 'static>(guard: G, files: Vec<Staged>) -> Result<()> {
    tokio::task::spawn_blocking(move || {
        let renamed = files.iter().try_for_each(|file| {
            if let Some(dir) = file.dest_path.parent() {
                std::fs::create_dir_all(dir)?;
            }
            std::fs::rename(&file.tmp_path, &file.dest_path)
        });
        drop(guard);
        renamed
    })
    .await??;
    Ok(())
}

impl Drop for FileWriter<'_> {
    fn drop(&mut self) {
        if self.clean_tmp {
            let _ = std::fs::remove_file(&self.tmp_path);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::{Arc, Barrier};

    struct TestRoot(PathBuf);

    impl Drop for TestRoot {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn concurrent_upload_part_info_deletion_is_idempotent() -> Result<()> {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .max_blocking_threads(1)
            .build()?;

        runtime.block_on(async {
            let root = env::temp_dir().join(format!("s3s-fs-part-info-cleanup-{}", Uuid::new_v4()));
            std::fs::create_dir_all(&root)?;
            let _root = TestRoot(root.clone());
            let file_system = FileSystem::new(&root)?;
            let upload_id = Uuid::new_v4();
            let part_number = 1;
            file_system
                .save_upload_part_info(upload_id, part_number, &InternalInfo::default())
                .await?;

            // Occupy the sole blocking worker so both deletions reach `remove_file` before either runs.
            let barrier = Arc::new(Barrier::new(2));
            let worker_barrier = Arc::clone(&barrier);
            let blocker = tokio::task::spawn_blocking(move || {
                worker_barrier.wait();
                worker_barrier.wait();
            });
            barrier.wait();

            let first = file_system.delete_upload_part_info(upload_id, part_number);
            let second = file_system.delete_upload_part_info(upload_id, part_number);
            tokio::pin!(first);
            tokio::pin!(second);
            let first_pending = futures::poll!(first.as_mut()).is_pending();
            let second_pending = futures::poll!(second.as_mut()).is_pending();
            barrier.wait();

            assert!(first_pending, "first deletion completed before reaching the blocking worker");
            assert!(second_pending, "second deletion completed before reaching the blocking worker");
            let first_result = first.await;
            let second_result = second.await;
            blocker.await.expect("blocking worker should finish");
            first_result?;
            second_result
        })
    }
}
