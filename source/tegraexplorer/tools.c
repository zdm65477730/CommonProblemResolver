#include "tools.h"
#include "../gfx/gfx.h"
#include "../gfx/gfxutils.h"
#include "../gfx/menu.h"
#include "../hid/hid.h"
#include <libs/fatfs/ff.h>
#include "../keys/keys.h"
#include "../keys/nca.h"
#include <storage/sd.h>
#include "../fs/fsutils.h"
#include <utils/util.h>
#include <display/di.h>
#include "../storage/mountmanager.h"
#include "../err.h"
#include <utils/sprintf.h>
#include <mem/heap.h>
#include "../tegraexplorer/tconf.h"
#include "../fs/readers/folderReader.h"
#include <string.h>
#include "../fs/fscopy.h"
#include "../utils/utils.h"
#include <soc/timer.h>

void DumpSysFw(){
	char sysPath[25 + 36 + 3 + 1]; // 24 for "bis:/Contents/registered", 36 for ncaName.nca, 3 for /00, and 1 to make sure :)
	char *baseSdPath;

	u32 timer = get_tmr_s();

	if (!sd_mount())
		return;

	if (connectMMC(MMC_CONN_EMMC))
		return;

	if (!TConf.keysDumped)
		return;

	ErrCode_t err = mountMMCPart("SYSTEM");
	if (err.err){
		DrawError(err);
		return;
	}

	baseSdPath = malloc(36 + 16);
	s_printf(baseSdPath, "sd:/tegraexplorer/Firmware/%d (%s)", TConf.pkg1ver, TConf.pkg1ID);
	int baseSdPathLen = strlen(baseSdPath);

	f_mkdir("sd:/tegraexplorer");
	f_mkdir("sd:/tegraexplorer/Firmware");

	gfx_clearscreen();

	gfx_printf("Pkg1 id: '%s', kb %d\n", TConf.pkg1ID, TConf.pkg1ver);
	if (FileExists(baseSdPath)){
		SETCOLOR(COLOR_ORANGE, COLOR_DEFAULT);
		gfx_printf("Destination already exists. Replace?   ");
		if (!MakeYesNoHorzMenu(3, COLOR_DEFAULT)){
			free(baseSdPath);
			return;
		}
		RESETCOLOR;
		gfx_printf("\nDeleting... ");
		FolderDelete(baseSdPath);
		gfx_putc('\n');
	}

	f_mkdir(baseSdPath);

	gfx_printf("Out: %s\nReading entries...\n", baseSdPath);
	int readRes = 0;
	Vector_t fileVec = ReadFolder("bis:/Contents/registered", &readRes);
	if (readRes){
		DrawError(newErrCode(readRes));
		free(baseSdPath);
		return;
	}

	gfx_printf("Starting dump...\n");
	SETCOLOR(COLOR_GREEN, COLOR_DEFAULT);

	int res = 0;
	int total = 1;
	vecDefArray(FSEntry_t*, fsEntries, fileVec);
	for (int i = 0; i < fileVec.count; i++){
		s_printf(sysPath, (fsEntries[i].isDir) ? "%s/%s/00" : "%s/%s", "bis:/Contents/registered", fsEntries[i].name);
		int contentType = GetNcaType(sysPath);

		if (contentType < 0){
			res = 1;
			break;
		}

		char *sdPath = malloc(baseSdPathLen + 45);
		s_printf(sdPath, "%s/%s", baseSdPath, fsEntries[i].name);
		if (contentType == Meta)
			memcpy(sdPath + strlen(sdPath) - 4, ".cnmt.nca", 10);
		
		gfx_printf("[%3d / %3d] %s\r", total, fileVec.count, fsEntries[i].name);
		total++;
		err = FileCopy(sysPath, sdPath, 0);
		free(sdPath);
		if (err.err){
			DrawError(err);
			res = 1;
			break;
		}
	}
	clearFileVector(&fileVec);

	RESETCOLOR;

	if (res){
		gfx_printf("\nDump failed...\n");
	}

	gfx_printf("\n\nDone! Time taken: %ds\nPress any key to exit", get_tmr_s() - timer);
	free(baseSdPath);
	hidWait();
}

extern sdmmc_storage_t sd_storage;


#include <string.h>
#include <stdlib.h>
#include "../config.h"
#include <libs/fatfs/diskio.h>
#include <storage/emmc.h>
#include "../storage/emummc.h"
#include <storage/sd.h>
#include <storage/nx_emmc_bis.h>

#define MBR_Table                       446             /* MBR: Offset of partition table in the MBR */
#define SZ_PTE                          16              /* MBR: Size of a partition table entry */
#define LEAVE_MKFS(res)	{ if (!work) ff_memfree(buf); return res; }


/* Fill memory block */
static void mem_set (void* dst, int val, UINT cnt)
{
	BYTE *d = (BYTE*)dst;

	do {
		*d++ = (BYTE)val;
	} while (--cnt);
}

static void st_word (BYTE* ptr, WORD val)	/* Store a 2-byte word in little-endian */
{
	*ptr++ = (BYTE)val; val >>= 8;
	*ptr++ = (BYTE)val;
}

static void st_dword (BYTE* ptr, DWORD val)	/* Store a 4-byte word in little-endian */
{
	*ptr++ = (BYTE)val; val >>= 8;
	*ptr++ = (BYTE)val; val >>= 8;
	*ptr++ = (BYTE)val; val >>= 8;
	*ptr++ = (BYTE)val;
}

FRESULT f_fdisk_mod (
	BYTE pdrv,			/* Physical drive number */
	const DWORD* szt,	/* Pointer to the size table for each partitions */
    void* work
)
{
	UINT i, n, sz_cyl, tot_cyl, e_cyl;
	BYTE s_hd, e_hd, *p, *buf = (BYTE*)work;
	DSTATUS stat;
	DWORD sz_disk, p_sect, b_cyl, b_sect;
	FRESULT res;

	stat = disk_initialize(pdrv);
	if (stat & STA_NOINIT) return FR_NOT_READY;
	if (stat & STA_PROTECT) return FR_WRITE_PROTECTED;
	sz_disk = sd_storage.csd.capacity;

	if (!buf) return FR_NOT_ENOUGH_CORE;

	/* Determine the CHS without any consideration of the drive geometry */
	for (n = 16; n < 256 && sz_disk / n / 63 > 1024; n *= 2) ;
	if (n == 256) n--;
	e_hd = (BYTE)(n - 1);
	sz_cyl = 63 * n;
	tot_cyl = sz_disk / sz_cyl;

	/* Create partition table */
	mem_set(buf, 0, 0x10000);
	p = buf + MBR_Table; b_cyl = 0, b_sect = 0;
	for (i = 0; i < 4; i++, p += SZ_PTE) {
		p_sect = szt[i]; /* Number of sectors */

		if (p_sect == 0)
			continue;

		if (i == 0) {	/* Exclude first 16MiB of sd */
			s_hd = 1;
			b_sect += 32768; p_sect -= 32768;
		}
		else
			s_hd = 0;

		b_cyl = b_sect / sz_cyl;
		e_cyl = ((b_sect + p_sect) / sz_cyl) - 1;	/* End cylinder */

		if (e_cyl >= tot_cyl)
			LEAVE_MKFS(FR_INVALID_PARAMETER);


		/* Set partition table */
		p[1] = s_hd;						/* Start head */
		p[2] = (BYTE)(((b_cyl >> 2) & 0xC0) | 1);	/* Start sector */
		p[3] = (BYTE)b_cyl;					/* Start cylinder */
		p[4] = 0x07;						/* System type (temporary setting) */
		p[5] = e_hd;						/* End head */
		p[6] = (BYTE)(((e_cyl >> 2) & 0xC0) | 63);	/* End sector */
		p[7] = (BYTE)e_cyl;					/* End cylinder */
		st_dword(p + 8, b_sect);			/* Start sector in LBA */
		st_dword(p + 12, p_sect);			/* Number of sectors */
		/* Next partition */

		for (u32 cursect = 0; cursect < 512; cursect++){
			disk_write(pdrv, buf + 0x4000, b_sect + (64 * cursect), 64);
		}

		b_sect += p_sect;
	}
	st_word(p, 0xAA55);		/* MBR signature (always at offset 510) */

	/* Write it to the MBR */
	res = (disk_write(pdrv, buf, 0, 1) == RES_OK && disk_ioctl(pdrv, CTRL_SYNC, 0) == RES_OK) ? FR_OK : FR_DISK_ERR;
	LEAVE_MKFS(res);
}


MenuEntry_t FatAndEmu[] = {
	{.optionUnion = COLORTORGB(COLOR_ORANGE), .name = "Back to main menu"},
	{.optionUnion = COLORTORGB(COLOR_GREEN), .name = "Fat32 + EmuMMC"},
	{.optionUnion = COLORTORGB(COLOR_BLUE), .name = "Only Fat32"}
};

void FormatSD(){
	gfx_clearscreen();
	disconnectMMC();
	DWORD plist[] = {0,0,0,0};
	bool emummc = 0;
	int res;

	if (!sd_get_card_initialized() || sd_get_card_removed())
		return;

	gfx_printf("\nDo you want to partition for an emummc?\n");
	res = MakeHorizontalMenu(FatAndEmu, ARR_LEN(FatAndEmu), 3, COLOR_DEFAULT, 0);
	
	if (!res)
		return;

	emummc = !(res - 1);
	
	SETCOLOR(COLOR_RED, COLOR_DEFAULT);

	plist[0] = sd_storage.csd.capacity;
	if (emummc){
		if (plist[0] < 83886080){
            gfx_printf("\n\nYou seem to be running this on a 32GB or smaller SD\nNot enough free space for emummc!");
			hidWait();
			return;
        }
		plist[0] -= 61145088;
		u32 allignedSectors = plist[0] - plist[0] % 2048;
		plist[1] = 61145088 + plist[0] % 2048;
		plist[0] = allignedSectors;
	}

	gfx_printf("\n\nAre you sure you want to format your sd?\nThis will delete everything on your SD card!\nThis action is irreversible!\n\n");
	WaitFor(1500);

	gfx_printf("%kAre you sure?   ", COLOR_WHITE);
	if (!MakeYesNoHorzMenu(3, COLOR_DEFAULT)){
		return;
	}

	RESETCOLOR;

	gfx_printf("\n\nStarting Partitioning & Formatting\n");

	for (int i = 0; i < 2; i++){
		gfx_printf("Part %d: %dKiB\n", i + 1, plist[i] / 2);
	}

	u8 *work = malloc(TConf.FSBuffSize);
	res = f_fdisk_mod(0, plist, work);

	if (!res){
		res = f_mkfs("sd:", FM_FAT32, 32768, work, TConf.FSBuffSize);
	}

	sd_unmount();

	if (res){
		DrawError(newErrCode(res));
		gfx_clearscreen();
		gfx_printf("Something went wrong\nPress any key to exit");
	}
	else {
		sd_mount();
		gfx_printf("\nDone!\nPress any key to exit");
	}

	free(work);
	hidWait();
}

void TakeScreenshot(){
    static u32 timer = 0;

    if (!TConf.minervaEnabled || !sd_get_card_mounted())
		return;

    if (timer + 3 < get_tmr_s())
        timer = get_tmr_s();
    else 
        return;

    char *name, *path;
    const char basepath[] = "sd:/tegraexplorer/screenshots";
    name = malloc(40);
    s_printf(name, "Screenshot_%08X.bmp", get_tmr_us());

    f_mkdir("sd:/tegraexplorer");
    f_mkdir(basepath);
    path = CombinePaths(basepath, name);
    free(name);

    const u32 file_size = 0x384000 + 0x36;
    u8 *bitmap = malloc(file_size);
    u32 *fb = malloc(0x384000);
    u32 *fb_ptr = gfx_ctxt.fb;

    for (int x = 1279; x >= 0; x--)
	{
		for (int y = 719; y >= 0; y--)
			fb[y * 1280 + x] = *fb_ptr++;
	}

    memcpy(bitmap + 0x36, fb, 0x384000);
    bmp_t *bmp = (bmp_t *)bitmap;

	bmp->magic    = 0x4D42;
	bmp->size     = file_size;
	bmp->rsvd     = 0;
	bmp->data_off = 0x36;
	bmp->hdr_size = 40;
	bmp->width    = 1280;
	bmp->height   = 720;
	bmp->planes   = 1;
	bmp->pxl_bits = 32;
	bmp->comp     = 0;
	bmp->img_size = 0x384000;
	bmp->res_h    = 2834;
	bmp->res_v    = 2834;
	bmp->rsvd2    = 0;

    sd_save_to_file(bitmap, file_size, path);
    free(bitmap);
    free(fb);
	free(path);

    display_backlight_brightness(255, 1000);
	msleep(100);
	display_backlight_brightness(100, 1000);
}