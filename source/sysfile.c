//
// File-system system calls.
// Mostly argument checking, since we don't trust
// user code, and calls into file.c and fs.c.
//

#include "types.h"
#include "riscv.h"
#include "defs.h"
#include "param.h"
#include "stat.h"
#include "spinlock.h"
#include "proc.h"
#include "fs.h"
#include "sleeplock.h"
#include "file.h"
#include "fcntl.h"
#include <stddef.h>


// Fetch the nth word-sized system call argument as a file descriptor
// and return both the descriptor and the corresponding struct file.
static int
argfd(int n, int *pfd, struct file **pf)
{
  int fd;
  struct file *f;

  argint(n, &fd);
  if(fd < 0 || fd >= NOFILE || (f=myproc()->ofile[fd]) == 0)
    return -1;
  if(pfd)
    *pfd = fd;
  if(pf)
    *pf = f;
  return 0;
}

// Allocate a file descriptor for the given file.
// Takes over file reference from caller on success.
static int
fdalloc(struct file *f)
{
  int fd;
  struct proc *p = myproc();

  for(fd = 0; fd < NOFILE; fd++){
    if(p->ofile[fd] == 0){
      p->ofile[fd] = f;
      return fd;
    }
  }
  return -1;
}

uint64
sys_dup(void)
{
  struct file *f;
  int fd;

  if(argfd(0, 0, &f) < 0)
    return -1;
  if((fd=fdalloc(f)) < 0)
    return -1;
  filedup(f);
  return fd;
}

uint64
sys_read(void)
{
  struct file *f;
  int n;
  uint64 p;

  argaddr(1, &p);
  argint(2, &n);
  if(argfd(0, 0, &f) < 0)
    return -1;
  return fileread(f, p, n);
}

uint64
sys_write(void)
{
  struct file *f;
  int n;
  uint64 p;
  
  argaddr(1, &p);
  argint(2, &n);
  if(argfd(0, 0, &f) < 0)
    return -1;

  return filewrite(f, p, n);
}

uint64
sys_close(void)
{
  int fd;
  struct file *f;

  if(argfd(0, &fd, &f) < 0)
    return -1;
  myproc()->ofile[fd] = 0;
  fileclose(f);
  return 0;
}

uint64
sys_fstat(void)
{
  struct file *f;
  uint64 st; // user pointer to struct stat

  argaddr(1, &st);
  if(argfd(0, 0, &f) < 0)
    return -1;
  return filestat(f, st);
}

// Create the path new as a link to the same inode as old.
uint64
sys_link(void)
{
  char name[DIRSIZ], new[MAXPATH], old[MAXPATH];
  struct inode *dp, *ip;

  if(argstr(0, old, MAXPATH) < 0 || argstr(1, new, MAXPATH) < 0)
    return -1;

  begin_op();
  if((ip = namei(old)) == 0){
    end_op();
    return -1;
  }

  ilock(ip);
  if(ip->type == T_DIR){
    iunlockput(ip);
    end_op();
    return -1;
  }

  ip->nlink++;
  iupdate(ip);
  iunlock(ip);

  if((dp = nameiparent(new, name)) == 0)
    goto bad;
  ilock(dp);
  if(dp->dev != ip->dev || dirlink(dp, name, ip->inum) < 0){
    iunlockput(dp);
    goto bad;
  }
  iunlockput(dp);
  iput(ip);

  end_op();

  return 0;

bad:
  ilock(ip);
  ip->nlink--;
  iupdate(ip);
  iunlockput(ip);
  end_op();
  return -1;
}

// Is the directory dp empty except for "." and ".." ?
static int
isdirempty(struct inode *dp)
{
  int off;
  struct dirent de;

  for(off=2*sizeof(de); off<dp->size; off+=sizeof(de)){
    if(readi(dp, 0, (uint64)&de, off, sizeof(de)) != sizeof(de))
      panic("isdirempty: readi");
    if(de.inum != 0)
      return 0;
  }
  return 1;
}

uint64
sys_unlink(void)
{
  struct inode *ip, *dp;
  struct dirent de;
  char name[DIRSIZ], path[MAXPATH];
  uint off;

  if(argstr(0, path, MAXPATH) < 0)
    return -1;

  begin_op();
  if((dp = nameiparent(path, name)) == 0){
    end_op();
    return -1;
  }

  ilock(dp);

  // Cannot unlink "." or "..".
  if(namecmp(name, ".") == 0 || namecmp(name, "..") == 0)
    goto bad;

  if((ip = dirlookup(dp, name, &off)) == 0)
    goto bad;
  ilock(ip);

  if(ip->nlink < 1)
    panic("unlink: nlink < 1");
  if(ip->type == T_DIR && !isdirempty(ip)){
    iunlockput(ip);
    goto bad;
  }

  memset(&de, 0, sizeof(de));
  if(writei(dp, 0, (uint64)&de, off, sizeof(de)) != sizeof(de))
    panic("unlink: writei");
  if(ip->type == T_DIR){
    dp->nlink--;
    iupdate(dp);
  }
  iunlockput(dp);

  ip->nlink--;
  iupdate(ip);
  iunlockput(ip);

  end_op();

  return 0;

bad:
  iunlockput(dp);
  end_op();
  return -1;
}

// TODO: complete mmap()
uint64 sys_mmap(void) {
    uint64 addr, size, offset;
    int protection, flags, fd;
    struct file *f = NULL;
    struct proc *p = myproc();

    // Fetch arguments
    argaddr(0, &addr);
    argaddr(1, &size);
    argint(2, &protection);
    argint(3, &flags);
    if (argfd(4, &fd, &f) < 0) {
        return -1;
    }
    argaddr(5, &offset);

    // Validate size and alignment
    if (size <= 0 || offset % PGSIZE != 0) {
        return -1;
    }

    // Choose address if unspecified
    if (addr == 0) {
        addr = PGROUNDUP(p->sz);
    } else if (addr % PGSIZE != 0) {
        return -1; // Ensure page alignment
    }

    // Map file offset and check for writable MAP_SHARED
    if ((protection & PROT_WRITE) && (flags & MAP_SHARED) && !f->writable) {
        return -1;
    }

    // Find a free VMA slot
    struct vma *vma = NULL;
    for (int i = 0; i < VMASIZE; i++) {
        if (!p->vma[i].valid) {
            vma = &p->vma[i];
            break;
        }
    }
    if (!vma) {
        return -1;
    }

    // Set VMA fields
    vma->start = addr;
    vma->length = size;
    vma->prot = protection;
    vma->flags = flags;
    vma->offset = offset;
    vma->f = f;
    vma->valid = 1;

    if (f) filedup(f);

    // Expand process size if necessary
    if (addr + size > p->sz) p->sz = addr + size;

    // Page permissions
    int perm = PTE_U;
    if (protection & PROT_READ) perm |= PTE_R;
    if (protection & PROT_WRITE) perm |= PTE_W;
    if (protection & PROT_EXEC) perm |= PTE_X;

    // Map pages with file contents, handling MAP_PRIVATE and MAP_SHARED
    begin_op();
    for (uint64 va = addr; va < addr + size; va += PGSIZE) {
        uint64 pa = (uint64)kalloc();
        if (pa == 0) {
            end_op();
            return -1;
        }
        memset((void *)pa, 0, PGSIZE);

        // Copy content from file starting at the specified offset
        if (flags & (MAP_SHARED | MAP_PRIVATE)) {
            ilock(f->ip);
            int n = readi(f->ip, 0, pa, offset + (va - addr), PGSIZE);
            iunlock(f->ip);

            if (n < 0) {
                end_op();
                kfree((void *)pa);
                return -1;
            }
        }

        if (mappages(p->pagetable, va, PGSIZE, pa, perm) < 0) {
            end_op();
            kfree((void *)pa);
            return -1;
        }
    }
    end_op();

    return addr;
}

// TODO: complete munmap()
uint64
sys_munmap(void) {
    struct proc *p = myproc();
    uint64 addr, length;

    // Retrieve arguments
    argaddr(0, &addr);
    argaddr(1, &length);

    // Validate length
    if (length <= 0) {
        return -1;
    }

    // Round up length to nearest page boundary
    uint64 unmap_limit = PGROUNDUP(addr + length);

    // Iterate through VMAs to locate overlapping regions
    for (int i = 0; i < VMASIZE; i++) {
        struct vma *vma = &p->vma[i];
        if (vma->valid && !(unmap_limit <= vma->start || addr >= vma->start + vma->length)) {
            
            uint64 start_unmap = addr > vma->start ? addr : vma->start;
            uint64 end_unmap = unmap_limit < (vma->start + vma->length) ? unmap_limit : (vma->start + vma->length);

            // If VMA is MAP_SHARED, write back modified pages to the file
            if (vma->f && (vma->flags & MAP_SHARED)) {
                begin_op();
                for (uint64 va = start_unmap; va < end_unmap; va += PGSIZE) {
                    pte_t *pte = walk(p->pagetable, va, 0);
                    if (pte && (*pte & PTE_V) && (*pte & PTE_R)) {
                        uint64 pa = PTE2PA(*pte);
                        char *kv = (char *)pa;

                        // Write back page and clear dirty bit
                        ilock(vma->f->ip);
                        int n = writei(vma->f->ip, 0, (uint64)kv, vma->offset + (va - vma->start), PGSIZE);
                        if (n != PGSIZE) {
                            printf("sys_munmap: writei failed for va=0x%p\n", va);
                        }
                        *pte &= ~PTE_R;  // Clear dirty bit
                        iunlock(vma->f->ip);
                    }
                }
                end_op();
            }

            // Free pages within this region
            int npages = (end_unmap - start_unmap) / PGSIZE;
            uvmunmap(p->pagetable, start_unmap, npages, 1);

            // Adjust or split the VMA as necessary
            if (start_unmap == vma->start && end_unmap == vma->start + vma->length) {
                vma->valid = 0;
                if (vma->f) {
                    fileclose(vma->f);
                    vma->f = 0;
                }
            } else if (start_unmap == vma->start) {
                vma->start = end_unmap;
                vma->offset += end_unmap - vma->start;
            } else if (end_unmap == vma->start + vma->length) {
                vma->length = start_unmap - vma->start;
            } else {
                int j;
                for (j = 0; j < VMASIZE; j++) {
                    if (!p->vma[j].valid) break;
                }
                if (j == VMASIZE) {
                    printf("sys_munmap: No free VMA slots available\n");
                    return -1;
                }

                p->vma[j] = *vma;
                p->vma[j].start = end_unmap;
                p->vma[j].length -= (end_unmap - vma->start);
                p->vma[j].offset += end_unmap - vma->start;
                vma->length = start_unmap - vma->start;
            }
        }
    }

    return 0;
}

static struct inode*
create(char *path, short type, short major, short minor)
{
  struct inode *ip, *dp;
  char name[DIRSIZ];

  if((dp = nameiparent(path, name)) == 0)
    return 0;

  ilock(dp);

  if((ip = dirlookup(dp, name, 0)) != 0){
    iunlockput(dp);
    ilock(ip);
    if(type == T_FILE && (ip->type == T_FILE || ip->type == T_DEVICE))
      return ip;
    iunlockput(ip);
    return 0;
  }

  if((ip = ialloc(dp->dev, type)) == 0){
    iunlockput(dp);
    return 0;
  }

  ilock(ip);
  ip->major = major;
  ip->minor = minor;
  ip->nlink = 1;
  iupdate(ip);

  if(type == T_DIR){  // Create . and .. entries.
    // No ip->nlink++ for ".": avoid cyclic ref count.
    if(dirlink(ip, ".", ip->inum) < 0 || dirlink(ip, "..", dp->inum) < 0)
      goto fail;
  }

  if(dirlink(dp, name, ip->inum) < 0)
    goto fail;

  if(type == T_DIR){
    // now that success is guaranteed:
    dp->nlink++;  // for ".."
    iupdate(dp);
  }

  iunlockput(dp);

  return ip;

 fail:
  // something went wrong. de-allocate ip.
  ip->nlink = 0;
  iupdate(ip);
  iunlockput(ip);
  iunlockput(dp);
  return 0;
}

uint64
sys_open(void)
{
  char path[MAXPATH];
  int fd, omode;
  struct file *f;
  struct inode *ip;
  int n;

  argint(1, &omode);
  if((n = argstr(0, path, MAXPATH)) < 0)
    return -1;

  begin_op();

  if(omode & O_CREATE){
    ip = create(path, T_FILE, 0, 0);
    if(ip == 0){
      end_op();
      return -1;
    }
  } else {
    if((ip = namei(path)) == 0){
      end_op();
      return -1;
    }
    ilock(ip);
    if(ip->type == T_DIR && omode != O_RDONLY){
      iunlockput(ip);
      end_op();
      return -1;
    }
  }

  if(ip->type == T_DEVICE && (ip->major < 0 || ip->major >= NDEV)){
    iunlockput(ip);
    end_op();
    return -1;
  }

  if((f = filealloc()) == 0 || (fd = fdalloc(f)) < 0){
    if(f)
      fileclose(f);
    iunlockput(ip);
    end_op();
    return -1;
  }

  if(ip->type == T_DEVICE){
    f->type = FD_DEVICE;
    f->major = ip->major;
  } else {
    f->type = FD_INODE;
    f->off = 0;
  }
  f->ip = ip;
  f->readable = !(omode & O_WRONLY);
  f->writable = (omode & O_WRONLY) || (omode & O_RDWR);

  if((omode & O_TRUNC) && ip->type == T_FILE){
    itrunc(ip);
  }

  iunlock(ip);
  end_op();

  return fd;
}

uint64
sys_mkdir(void)
{
  char path[MAXPATH];
  struct inode *ip;

  begin_op();
  if(argstr(0, path, MAXPATH) < 0 || (ip = create(path, T_DIR, 0, 0)) == 0){
    end_op();
    return -1;
  }
  iunlockput(ip);
  end_op();
  return 0;
}

uint64
sys_mknod(void)
{
  struct inode *ip;
  char path[MAXPATH];
  int major, minor;

  begin_op();
  argint(1, &major);
  argint(2, &minor);
  if((argstr(0, path, MAXPATH)) < 0 ||
     (ip = create(path, T_DEVICE, major, minor)) == 0){
    end_op();
    return -1;
  }
  iunlockput(ip);
  end_op();
  return 0;
}

uint64
sys_chdir(void)
{
  char path[MAXPATH];
  struct inode *ip;
  struct proc *p = myproc();
  
  begin_op();
  if(argstr(0, path, MAXPATH) < 0 || (ip = namei(path)) == 0){
    end_op();
    return -1;
  }
  ilock(ip);
  if(ip->type != T_DIR){
    iunlockput(ip);
    end_op();
    return -1;
  }
  iunlock(ip);
  iput(p->cwd);
  end_op();
  p->cwd = ip;
  return 0;
}

uint64
sys_exec(void)
{
  char path[MAXPATH], *argv[MAXARG];
  int i;
  uint64 uargv, uarg;

  argaddr(1, &uargv);
  if(argstr(0, path, MAXPATH) < 0) {
    return -1;
  }
  memset(argv, 0, sizeof(argv));
  for(i=0;; i++){
    if(i >= NELEM(argv)){
      goto bad;
    }
    if(fetchaddr(uargv+sizeof(uint64)*i, (uint64*)&uarg) < 0){
      goto bad;
    }
    if(uarg == 0){
      argv[i] = 0;
      break;
    }
    argv[i] = kalloc();
    if(argv[i] == 0)
      goto bad;
    if(fetchstr(uarg, argv[i], PGSIZE) < 0)
      goto bad;
  }

  int ret = exec(path, argv);

  for(i = 0; i < NELEM(argv) && argv[i] != 0; i++)
    kfree(argv[i]);

  return ret;

 bad:
  for(i = 0; i < NELEM(argv) && argv[i] != 0; i++)
    kfree(argv[i]);
  return -1;
}

uint64
sys_pipe(void)
{
  uint64 fdarray; // user pointer to array of two integers
  struct file *rf, *wf;
  int fd0, fd1;
  struct proc *p = myproc();

  argaddr(0, &fdarray);
  if(pipealloc(&rf, &wf) < 0)
    return -1;
  fd0 = -1;
  if((fd0 = fdalloc(rf)) < 0 || (fd1 = fdalloc(wf)) < 0){
    if(fd0 >= 0)
      p->ofile[fd0] = 0;
    fileclose(rf);
    fileclose(wf);
    return -1;
  }
  if(copyout(p->pagetable, fdarray, (char*)&fd0, sizeof(fd0)) < 0 ||
     copyout(p->pagetable, fdarray+sizeof(fd0), (char *)&fd1, sizeof(fd1)) < 0){
    p->ofile[fd0] = 0;
    p->ofile[fd1] = 0;
    fileclose(rf);
    fileclose(wf);
    return -1;
  }
  return 0;
}
