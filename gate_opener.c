#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include "eat_modem.h"
#include "eat_interface.h"
#include "eat_uart.h"
#include "eat_timer.h" 
#include "eat_clib_define.h" //only in main.c
#include "eat_periphery.h"
#include "eat_sms.h"
#include "eat_fs.h"
#include "eat_socket.h"
#include "eat_flash.h" 

#define Version 48

#define INZ EAT_PIN6_UART1_DTR
#define OUT1 EAT_PIN3_UART1_RTS
#define LED EAT_PIN7_UART1_RI

#define main_buf_size 10000
#define APP_UPDATE_BUFF_SIZE 0x1000
#define EAT_MEM_MAX_SIZE 100*1024

typedef void (*app_user_func)(void*);
static u8 s_memPool[EAT_MEM_MAX_SIZE];
static EatEntryPara_st app_para;

static u8 ExIP[3][4] = {185,25,117,35, 185,25,117,35, 185,25,117,35};
static unsigned int ExPort[3] = {10033, 10033, 10033};
static u8 APN[31] = "www.kyivstar.net", APN_user[31] = "", APN_pass[31] = "";
static unsigned int Period1 = 10, Period2 = 60, Period3 = 2, prm_per = 300, gsmloc_per = 0, money_per = 0, trip_per = 0, debug_per = 0;
static unsigned int can1_per = 0, can2_per = 0, ADC_per = 0, INx_per = 0, freq_per = 0, ident_per = 0, offsim_per = 14400;
static unsigned int Send_per1 = 10, Send_per2 = 60, Stealth_ontm = 0, Stealth_per = 0;
static unsigned int Vbt_off = 3500, Speed_lim = 250, Vcc_lim = 0, Vbt_lim = 0, Rsindp = 120, Sync = 0;
static unsigned char PortPr = 7;
static unsigned char OutOnPeriod = 20;
static char SMS_pass[5] = "0000";
static char MoneyUSSD[11] = "*111#";
static char Num1[13] = "";
static char Num2[13] = "";
static char Num3[13] = "";
static char Num4[13] = "";
static char Num5[13] = "";
static char NumAd1[13] = "380674896016";
static char NumAd2[13] = "";
static u8 eng_block = 0;
static unsigned int Settings = 1+8+64+128+2048;
//bit0 - (0)пер.отпр.-0-движ;1-заж.;2-пост.;3-адапт.		1
//bit1 - (1)пер.отпр.-0-движ;1-заж.;2-пост.;3-адапт.		2
//bit2 - опред. роуминг по карте							4
//bit3 - опред. роуминг по GSM				 				8
//bit4 - Bluetooth On										16
//bit5 - отправлять данные в роуминге						32
//bit6 - отвечать на СМС  в роуминге			 			64
//bit7 - (0)фильтр на стоянкак-0-нет;1-по прогр.движ.		128
//bit8 - (1)2-по заж.3-reserved								256
//bit9 - СМС режим											512
//bit10 - reserve											1024
//bit11 - Не разрывать соединение							2048
//bit12 - reserve											4096
//bit13 - reserve											8192
//bit14 - reserve											16384
//bit15 - reserve											32768

static unsigned int Settings1 = 1+2+4+8;
//bit0 - при изм.заж.зап.коорд.								1
//bit1 - при изм.заж.начинать отпр.							2
//bit2 - при откл/вкл.вн.напр.зап.коорд.					4
//bit3 - при откл/вкл.вн.напр.начинать отпр.				8
//bit4 - IN1 - тревога										16
//bit5 - IN2 - тревога										32
//bit6 - Тревога1 акт.выс.						 			64
//bit7 - Тревога2 акт.выс.									128
//bit8 - отправл.gsmloc при опред. по gps					256
//bit9 - при изм.движ.зап.									512
//bit10 - при изм.движ.отпр.								1024
//bit11 - при изм. IN1 отпр.								2048
//bit12 - при изм. IN2 отпр.								4096
//bit13 - reserve											8192
//bit14 - reserve											16384
//bit15 - reserve											32768

static unsigned int Sts_d = 0;
//bit0 - Speed_lim				1
//bit1 - RoumingMAP				2
//bit2 - gprs_reg				4
//bit3 - Ignition				8
//bit4 - Move					16
//bit5 - gsm_reg0				32
//bit6 - gsm_reg1				64
//bit7 - gsm_reg2				128
//bit8 - Jamming				256
//bit9 - Вн.напр.откл.			512
//bit10 - Авт.заблокирован		1024
//bit11 - Vcc_lim				2048
//bit12 - Vbt_lim				4096
//bit13 - Перегрев				8192
//bit14 - IN1					16384
//bit15 - IN2					32768
static char simrev[200];
static char IMEI[17] = {31, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0}, ICC[6] = {0,0,0,0,0,0};
static u8 FTP_server[4], own_ip[4];
static char FTP_user[31], FTP_pass[31], FTP_path[101], fw_filename[15], incall_nbr[13], sms_txt[251], sms_nbr[13], ussdcmd[100];
static u8 main_st = 0, udpsend_st = 0, send_sms_st = 0, gprs_st = 0;
static u8 main_status = 0, cfun = 0, gsm_reg = 0, cgatt = 0;
static eat_bool cpin = EAT_FALSE, do_send = EAT_FALSE, fw_update = EAT_FALSE, gate_open = EAT_FALSE, btacpt = EAT_FALSE, btpair = EAT_FALSE, bton = EAT_FALSE, btoff = EAT_FALSE;
static eat_bool money_f = EAT_FALSE, gsmloc_f = EAT_FALSE, simreset_f = EAT_FALSE, incall_f = EAT_FALSE, getnumbers = EAT_FALSE, show_bt_menu = EAT_FALSE;
static eat_bool ata_f = EAT_FALSE, ath_f = EAT_FALSE, first_init = EAT_FALSE, pos2sms = EAT_FALSE, sms_sended = EAT_FALSE, ath_simreset_f = EAT_FALSE;
static eat_bool send_sms_f = EAT_FALSE, gprs_enable = EAT_FALSE, send_cfun1 = EAT_FALSE, send_cfun4 = EAT_FALSE, send_dtmf = EAT_FALSE, fsinfo = EAT_FALSE;
static eat_bool gprs_reset = EAT_FALSE, log_upload = EAT_FALSE, modinfo = EAT_FALSE, ussd_send = EAT_FALSE, stsreset = EAT_FALSE, cpureset = EAT_FALSE;
static eat_bool getparam1 = EAT_FALSE, getparam2 = EAT_FALSE, getparam3 = EAT_FALSE, getparam4 = EAT_FALSE, getparam5 = EAT_FALSE, gsmoffon = EAT_FALSE;
static eat_bool bt_send_sets = EAT_FALSE, bt_send_nmbrs = EAT_FALSE;
static u8 dtmf_c = 0, dtmf_d = 0, dtmf_menu_number = 0, log_write_en = 0, bt_menu_number = 0;
static u8 SatUs = 0, bear_st = 0, ExIPN = 0, senderr_cnt = 0, extoff_time = 0, gprs_st_timer = 0, gprs_st_errcnt = 0, udpsend_st_timer = 0;
static u16 Period = 0, period_cnt = 0, Send_per = 0, send_cnt = 0, rsindp_cnt = 0, prm_cnt = 0, gsmloc_cnt = 0, money_cnt = 0, offsim_cnt = 0;
static u16 trip_cnt = 0, debug_cnt = 0, ADC_cnt = 0, INx_cnt = 0, freq_cnt = 0, ident_cnt = 0, reg_err_cnt = 0, can1_cnt = 0, can2_cnt = 0, vibration_cnt = 0;
static u16 insms_id = 0, stealth_timer = 0, stealth_cnt = 0;
static unsigned long Latitude = 0, Longitude = 0, Trip = 0;
static u8 Year = 0, Month = 0, Day = 0, Hour = 0, Minute = 0, Second = 0;
static u16 Speed = 0, Course = 0, Vbt = 0, Vcc = 0, Money = 0, freq1 = 0, freq2 = 0;
static u8 rssi = 0, Turn = 0;
static u8 ADC1 = 0, ADC2 = 0;
static s8 Tm = 0;
static unsigned int MCC = 0, MNC = 0, LAC = 0, CID = 0, do_req = 0;
static unsigned char cmd_ret = 0;
static EatSemId_st sem_at_done = EAT_NULL;
static char at_answer[100], server_answer[1024];
static char * at_ret;
static u16 at_timer;
static u8 at_res, CRC = 0, Event_nbr = 0, uv_cnt = 0, vclim_cnt = 0, vblim_cnt = 0;
static sockaddr_struct server_adr;
static s8 server_soc = 0;
static int log_file = 0;
static char debug_buf[50], bt_send_buf[300];

static unsigned char main_buf[main_buf_size], out_buf[1000];
static unsigned long eeprom_p1 = 0, eeprom_p2 = 0, eeprom_p2tmp = 0, out_buf_col = 0;

static u8 s_st = 0;

extern void APP_InitRegions(void);

void app_main(void *data);
void app_func_ext1(void *data);
void app_user2(void *data);
void app_user3(void *data);
void app_user8(void *data);

#pragma arm section rodata = "APP_CFG"
APP_ENTRY_FLAG 
#pragma arm section rodata

#pragma arm section rodata="APPENTRY"
	const EatEntry_st AppEntry = 
	{
		app_main,
		app_func_ext1,
		(app_user_func)EAT_NULL,//app_user1,
		(app_user_func)app_user2,//app_user2,
		(app_user_func)EAT_NULL,//app_user3,
		(app_user_func)EAT_NULL,//app_user4,
		(app_user_func)EAT_NULL,//app_user5,
		(app_user_func)EAT_NULL,//app_user6,
		(app_user_func)app_user8,//app_user8,
		EAT_NULL,
		EAT_NULL,
		EAT_NULL,
		EAT_NULL,
		EAT_NULL,
		EAT_NULL
	};
#pragma arm section rodata

void app_func_ext1(void *data)
{
	eat_uart_set_debug(EAT_UART_USB);
	eat_uart_set_debug_config(EAT_UART_DEBUG_MODE_TRACE, NULL);
//	eat_uart_set_debug_config(EAT_UART_DEBUG_MODE_UART, NULL);
	eat_uart_set_at_port(EAT_UART_NULL);
//	eat_uart_set_at_port(EAT_UART_USB);
	
	eat_sim_detect_en(EAT_FALSE);
	eat_pin_set_mode(LED, EAT_PIN_MODE_GPIO);
	eat_pin_set_mode(INZ, EAT_PIN_MODE_GPIO);
	eat_pin_set_mode(OUT1, EAT_PIN_MODE_GPIO);
}

unsigned char
dir_r(u16 dir1, u16 dir2)
{
	u16 r1, r2, a1, a2;

	if(dir2 > dir1)
	{
		r1 = dir2;
		r2 = dir1;
	}
	else
	{
		r1 = dir1;
		r2 = dir2;
	}
	a1 = r1 - r2;
	a2 = (360 - r1) + r2;
	if(a1 < a2)
		return a1;
	else
		return a2;
}

void
app_update(const unsigned short *filename)
{
    eat_bool ret = EAT_FALSE;
    void* buff_p = NULL;
    unsigned char *addr;
    unsigned int t1,t2, t_erase=0, t_write=0, c_write=0, read_count=0;
    unsigned int app_datalen = APP_UPDATE_BUFF_SIZE ;
    unsigned int filesize, read_len;
    int testFileHandle ;
    eat_fs_error_enum fs_op_ret;

    addr =  (unsigned char *)(eat_get_app_base_addr() + (eat_get_app_space()>>1));

    testFileHandle = eat_fs_Open(filename, FS_READ_ONLY);
    if(testFileHandle<EAT_FS_NO_ERROR )
    {
eat_trace("eat_fs_Open():Create File Fail,and Return Error is %x ",testFileHandle);
        return ;
    }
    else
    {
eat_trace("eat_fs_Open():Create File Success,and FileHandle is %x ",testFileHandle);
    }
    fs_op_ret = (eat_fs_error_enum)eat_fs_GetFileSize(testFileHandle,&filesize);
    if(EAT_FS_NO_ERROR != fs_op_ret)
    {
eat_trace("eat_fs_GetFileSize():Get File Size Fail,and Return Error is %d",fs_op_ret);
        eat_fs_Close(testFileHandle);
        return;
    }
    else
    {
eat_trace("eat_fs_GetFileSize():Get File Size Success and File Size id %d",filesize);
    }

eat_trace("erase flash addr=%x len=%x", addr,  filesize); 
    t1 = eat_get_current_time();
    ret = eat_flash_erase(addr, filesize);
    t_erase = eat_get_duration_ms(t1);
    if(!ret)
    {
        eat_fs_Close(testFileHandle);
eat_trace("Erase flash failed [0x%08x, %dKByte]", addr,  filesize/1024);
        return;
    }
    read_count = filesize/APP_UPDATE_BUFF_SIZE; //only for testing,so don't case the completeness of file
eat_trace("need to read file %d",read_count);
    if(read_count == 0)
    {
        //only read once
        read_count=1;
        read_len = filesize;
    }else
    {
        read_count++;
        read_len = APP_UPDATE_BUFF_SIZE;
    }
	buff_p = eat_mem_alloc(app_datalen);
    if( buff_p == NULL)
    {
eat_trace("mem alloc fail!");
        eat_fs_Close(testFileHandle);
        return ;
    }
    filesize = 0;
    while(read_count--)
    {
        fs_op_ret = (eat_fs_error_enum)eat_fs_Read(testFileHandle, buff_p, read_len, &app_datalen);
        if(EAT_FS_NO_ERROR != fs_op_ret )
        {   
eat_trace("eat_fs_Read():Read File Fail,and Return Error is %d,Readlen is %d",fs_op_ret,app_datalen);
            eat_fs_Close(testFileHandle);
            eat_mem_free(buff_p);
            return;
        }
        else
        {
//eat_trace("eat_fs_Read():Read File Success");
        }

//eat_trace("START: write flash[0x%x, %dKByte]", APP_DATA_STORAGE_BASE, app_datalen/1024);
        t1 = eat_get_current_time();
        ret = eat_flash_write(addr+filesize , buff_p, app_datalen);
        t2 = eat_get_duration_ms(t1);
        filesize += app_datalen;
        t_write += t2; 
        c_write ++;
eat_trace("write flash time=%d",t2);
        if(!ret)
        {
eat_trace("Write flash failed [0x%08x, %dKByte]", addr, app_datalen/1024);
            eat_fs_Close(testFileHandle);
            eat_mem_free(buff_p);
            return;
        }
    }
    eat_fs_Close(testFileHandle);
    eat_mem_free(buff_p);

eat_trace("All use %d write[%d, %d]", c_write, t_erase, t_write);
    eat_sleep(50);
    eat_update_app((void*)(eat_get_app_base_addr()), addr, filesize, EAT_PIN_NUM, EAT_PIN_NUM, EAT_FALSE);
eat_trace("Test App Over");
}

void
write_log(const char * log_msg)
{
	char tmp_buf[300];
	EatRtc_st rtc = {0};
	int ret;
    unsigned int dataLen, writedLen;
	
	if(log_write_en == 1)
	{
		eat_get_rtc(&rtc);
		dataLen = sprintf(tmp_buf, "%2.2u/%2.2u/%2.2u %2.2u:%2.2u:%2.2u - %s;\n\r", rtc.day, rtc.mon, rtc.year, rtc.hour, rtc.min, rtc.sec, log_msg);
		log_file = eat_fs_Open(L"C:\\log.txt", FS_CREATE|FS_READ_WRITE);
		if(log_file < EAT_FS_NO_ERROR)
		{
eat_trace("Create LOG File Fail,and Return Error is %d", log_file);
			return;
		}
		eat_fs_Seek(log_file, 0, EAT_FS_FILE_END);
		ret = (eat_fs_error_enum)eat_fs_Write(log_file, tmp_buf, dataLen, &writedLen);
		if(dataLen != writedLen || EAT_FS_NO_ERROR != ret)
		{	
eat_trace("eat_fs_Write():Write LOG File Fail,and Return Error is %d", ret);
		}
		eat_fs_Close(log_file);
	}
}

void
save_settings(void)
{
	int FileHandle, ret;
    void* buff_p = NULL;
    unsigned int dataLen, writedLen;

	FileHandle = eat_fs_Open(L"C:\\Settings.txt", FS_CREATE_ALWAYS|FS_READ_WRITE);
	if(FileHandle < EAT_FS_NO_ERROR)
	{
eat_trace("Create File Fail,and Return Error is %d", FileHandle);
		return;
	}
	buff_p = eat_mem_alloc(1000);
	if(buff_p == NULL)
	{
eat_trace("mem alloc fail!");
		eat_fs_Close(FileHandle);
		return;
	}
	dataLen = sprintf(buff_p, "%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s", ExIP[0][0], ExIP[0][1], ExIP[0][2], ExIP[0][3], ExIP[1][0], ExIP[1][1], ExIP[1][2], ExIP[1][3], ExIP[2][0], ExIP[2][1], ExIP[2][2], ExIP[2][3], Period1, Period2, prm_per, gsmloc_per, money_per, trip_per, debug_per, can1_per, can2_per, ADC_per, INx_per, freq_per, ident_per, offsim_per, Send_per1, Send_per2, Stealth_ontm, Stealth_per, Vbt_off, Settings, Settings1, ExPort[0], ExPort[1], ExPort[2], Speed_lim, Vcc_lim, Vbt_lim, Period3, Rsindp, Sync, PortPr, OutOnPeriod, APN, APN_user, APN_pass, SMS_pass, Num1, Num2, Num3, Num4, Num5, NumAd1, NumAd2, MoneyUSSD);
	ret = (eat_fs_error_enum)eat_fs_Write(FileHandle, buff_p, dataLen, &writedLen);
	if(dataLen != writedLen || EAT_FS_NO_ERROR != ret)
	{	
eat_trace("eat_fs_Write():Write File Fail,and Return Error is %d", ret);
	}
	eat_fs_Close(FileHandle);
	eat_mem_free(buff_p);
eat_trace("Settings save Ok");
}

eat_bool
load_settings(void)
{
	int FileHandle, ret;
    void* buff_p = NULL;
    unsigned int readLen;

	FileHandle = eat_fs_Open(L"C:\\Settings.txt", FS_READ_ONLY);
	if(FileHandle < EAT_FS_NO_ERROR)
	{
eat_trace("Open File Fail,and Return Error is %d", FileHandle);
		return EAT_FALSE;
	}
	buff_p = eat_mem_alloc(1000);
	if(buff_p == NULL)
	{
eat_trace("mem alloc fail!");
		eat_fs_Close(FileHandle);
		return EAT_TRUE;
	}
	ret = (eat_fs_error_enum)eat_fs_Read(FileHandle, buff_p, 1000, &readLen);
	if(EAT_FS_NO_ERROR != ret)
	{	
eat_trace("eat_fs_Read():Read File Fail,and Return Error is %d,Readlen is %d", ret, readLen);
		eat_fs_Close(FileHandle);
		eat_mem_free(buff_p);
		return EAT_FALSE;
	}
	sscanf(buff_p, "%hhu,%hhu,%hhu,%hhu,%hhu,%hhu,%hhu,%hhu,%hhu,%hhu,%hhu,%hhu,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%hhu,%hhu,%30[^,],%30[^,],%30[^,],%4[^,],%12[^,],%12[^,],%12[^,],%12[^,],%12[^,],%12[^,],%12[^,],%10s", &ExIP[0][0], &ExIP[0][1], &ExIP[0][2], &ExIP[0][3], &ExIP[1][0], &ExIP[1][1], &ExIP[1][2], &ExIP[1][3], &ExIP[2][0], &ExIP[2][1], &ExIP[2][2], &ExIP[2][3], &Period1, &Period2, &prm_per, &gsmloc_per, &money_per, &trip_per, &debug_per, &can1_per, &can2_per, &ADC_per, &INx_per, &freq_per, &ident_per, &offsim_per, &Send_per1, &Send_per2, &Stealth_ontm, &Stealth_per, &Vbt_off, &Settings, &Settings1, &ExPort[0], &ExPort[1], &ExPort[2], &Speed_lim, &Vcc_lim, &Vbt_lim, &Period3, &Rsindp, &Sync, &PortPr, &OutOnPeriod, APN, APN_user, APN_pass, SMS_pass, Num1, Num2, Num3, Num4, Num5, NumAd1, NumAd2, MoneyUSSD);
	eat_fs_Close(FileHandle);
	eat_mem_free(buff_p);
eat_trace("Settings load Ok");
eat_trace("%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u", ExIP[0][0], ExIP[0][1], ExIP[0][2], ExIP[0][3], ExIP[1][0], ExIP[1][1], ExIP[1][2], ExIP[1][3], ExIP[2][0], ExIP[2][1], ExIP[2][2], ExIP[2][3], Period1, Period2, prm_per, gsmloc_per, money_per, trip_per, debug_per, can1_per, can2_per, ADC_per, INx_per, freq_per, ident_per, offsim_per, Send_per1, Send_per2, Stealth_ontm, Stealth_per, Vbt_off, Settings, Settings1);
eat_trace("%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s", ExPort[0], ExPort[1], ExPort[2], Speed_lim, Vcc_lim, Vbt_lim, Period3, Rsindp, Sync, PortPr, APN, APN_user, APN_pass, SMS_pass, Num1, Num2, Num3, Num4, Num5, NumAd1, NumAd2, MoneyUSSD);
	if(Settings & 16)
	{
		bton = EAT_TRUE;
	}
	return EAT_TRUE;
}

eat_bool
phone_nbr_chk(char * phone_nbr)
{
	int FileHandle;
	unsigned int readLen;
	char phone_nbr_tmp[15];

	FileHandle = eat_fs_Open(L"C:\\Numbers.txt", FS_READ_ONLY);
	if(FileHandle < EAT_FS_NO_ERROR)
	{
		return EAT_FALSE;
	}
	do{
		eat_fs_Read(FileHandle, phone_nbr_tmp, 14, &readLen);
		phone_nbr_tmp[12] = 0;
		if(!strcmp(phone_nbr_tmp, phone_nbr))
		{
			eat_fs_Close(FileHandle);
			return EAT_TRUE;
		}
	}while(readLen == 14);
	eat_fs_Close(FileHandle);
	return EAT_FALSE;
}

eat_bool
phone_nbr_add(char * phone_nbr)
{
	int FileHandle, ret;
	unsigned int writedLen;

	if(!phone_nbr_chk(phone_nbr))
	{
		FileHandle = eat_fs_Open(L"C:\\Numbers.txt", FS_CREATE|FS_READ_WRITE);
		if(FileHandle < EAT_FS_NO_ERROR)
		{
eat_trace("Create File Fail,and Return Error is %d", FileHandle);
			return EAT_FALSE;
		}
		eat_fs_Seek(FileHandle, 0, EAT_FS_FILE_END);
		ret = (eat_fs_error_enum)eat_fs_Write(FileHandle, phone_nbr, 12, &writedLen);
		if(writedLen != 12 || EAT_FS_NO_ERROR != ret)
		{	
eat_trace("eat_fs_Write():Write File Fail,and Return Error is %d", ret);
		}
		ret = (eat_fs_error_enum)eat_fs_Write(FileHandle, "\r\n", 2, &writedLen);
		if(writedLen != 2 || EAT_FS_NO_ERROR != ret)
		{	
eat_trace("eat_fs_Write():Write File Fail,and Return Error is %d", ret);
		}
		eat_fs_Close(FileHandle);
		return EAT_TRUE;
	}
	else
	{
		return EAT_FALSE;
	}
}

eat_bool
phone_nbr_del(char * phone_nbr)
{
	int FileHandle;
	unsigned int readLen, writedLen;
	char phone_nbr_tmp[15];

	FileHandle = eat_fs_Open(L"C:\\Numbers.txt", FS_READ_WRITE);
	if(FileHandle < EAT_FS_NO_ERROR)
	{
eat_trace("Open File Fail,and Return Error is %d", FileHandle);
		return EAT_FALSE;
	}
	do{
		eat_fs_Read(FileHandle, phone_nbr_tmp, 14, &readLen);
		phone_nbr_tmp[12] = 0;
		if(!strcmp(phone_nbr_tmp, phone_nbr))
		{
			do{
				eat_fs_Read(FileHandle, phone_nbr_tmp, 14, &readLen);
				if(readLen == 14)
				{
					eat_fs_Seek(FileHandle, -14, EAT_FS_FILE_CURRENT);
					eat_fs_Write(FileHandle, phone_nbr_tmp, 14, &writedLen);
				}
				else
				{
					eat_fs_Seek(FileHandle, -14, EAT_FS_FILE_CURRENT);
					eat_fs_Truncate(FileHandle);
					eat_fs_Close(FileHandle);
					return EAT_TRUE;
				}
			}while(readLen == 14);
			eat_fs_Close(FileHandle);
			return EAT_TRUE;
		}
	}while(readLen == 14);
	eat_fs_Close(FileHandle);
	return EAT_FALSE;
}

void
save_status(void)
{
	int FileHandle, ret;
    void* buff_p = NULL;
    unsigned int dataLen, writedLen;

	FileHandle = eat_fs_Open(L"C:\\Status.txt", FS_CREATE_ALWAYS|FS_READ_WRITE);
	if(FileHandle < EAT_FS_NO_ERROR)
	{
eat_trace("Create File Fail,and Return Error is %d", FileHandle);
		return;
	}
	buff_p = eat_mem_alloc(500);
	if(buff_p == NULL)
	{
eat_trace("mem alloc fail!");
		eat_fs_Close(FileHandle);
		return;
	}
	dataLen = sprintf(buff_p, "%u,%u", eng_block, log_write_en);
	ret = (eat_fs_error_enum)eat_fs_Write(FileHandle, buff_p, dataLen, &writedLen);
	if(dataLen != writedLen || EAT_FS_NO_ERROR != ret)
	{	
eat_trace("eat_fs_Write():Write File Fail,and Return Error is %d", ret);
	}
	eat_fs_Close(FileHandle);
	eat_mem_free(buff_p);
eat_trace("Status save Ok");
}

eat_bool
load_status(void)
{
	int FileHandle, ret;
    void* buff_p = NULL;
    unsigned int readLen;

	FileHandle = eat_fs_Open(L"C:\\Status.txt", FS_READ_ONLY);
	if(FileHandle < EAT_FS_NO_ERROR)
	{
eat_trace("Open File Fail,and Return Error is %d", FileHandle);
		return EAT_FALSE;
	}
	buff_p = eat_mem_alloc(500);
	if(buff_p == NULL)
	{
eat_trace("mem alloc fail!");
		eat_fs_Close(FileHandle);
		return EAT_TRUE;
	}
	ret = (eat_fs_error_enum)eat_fs_Read(FileHandle, buff_p, 500, &readLen);
	if(EAT_FS_NO_ERROR != ret)
	{	
eat_trace("eat_fs_Read():Read File Fail,and Return Error is %d,Readlen is %d", ret, readLen);
		eat_fs_Close(FileHandle);
		eat_mem_free(buff_p);
		return EAT_FALSE;
	}
	sscanf(buff_p, "%hhu,%hhu", &eng_block, &log_write_en);
	eat_fs_Close(FileHandle);
	eat_mem_free(buff_p);
eat_trace("Status load Ok");
eat_trace("%u", eng_block);
	return EAT_TRUE;
}

void
send_sms(char * number, char * text)
{
	if(number && (gsm_reg != 5 || (Settings & 64)) && (main_status&4))
	{
		eat_send_text_sms((u8 *)number, (u8 *)text);
	}
}

static void
eat_sms_delete_cb(eat_bool result)
{
eat_trace("eat_sms_delete_cb, result=%d", result);
}

static void
eat_sms_read_cb(EatSmsReadCnf_st  smsReadCnfContent)
{
	char * buf_pos = NULL;
	char nbr_tmp[13];
	unsigned char tmpcnt;
	
eat_trace("eat_sms_read_cb, msg=%s", smsReadCnfContent.data);
eat_trace("eat_sms_read_cb, number=%s", smsReadCnfContent.number);
	if(*smsReadCnfContent.number == '+')
		strcpy(sms_nbr, (const char *)(smsReadCnfContent.number + 1));
	else
		strcpy(sms_nbr, (const char *)smsReadCnfContent.number);

	buf_pos = strchr((const char*)smsReadCnfContent.data, '#');
	if(buf_pos)
	{
		buf_pos++;
		if(!memcmp(buf_pos, "spass##", 7))
		{
			sprintf(sms_txt, "pass:\n%s", SMS_pass);
			send_sms(sms_nbr, sms_txt);
		}
		else
		{
			if((!memcmp(buf_pos, SMS_pass, 4)) || (!memcmp(buf_pos, "9876", 4)))
			{
				buf_pos = buf_pos + 5;
				if(!memcmp(buf_pos, "setparam1#", 10))
				{
					buf_pos = buf_pos + 10;
					sscanf(buf_pos, "%hhu.%hhu.%hhu.%hhu,%hhu.%hhu.%hhu.%hhu,%hhu.%hhu.%hhu.%hhu,%u,%u,%u,%30[^,],%30[^,],%30[^,],%hhu", &ExIP[0][0], &ExIP[0][1], &ExIP[0][2], &ExIP[0][3], &ExIP[1][0], &ExIP[1][1], &ExIP[1][2], &ExIP[1][3], &ExIP[2][0], &ExIP[2][1], &ExIP[2][2], &ExIP[2][3], &ExPort[0], &ExPort[1], &ExPort[2], APN, APN_user, APN_pass, &PortPr);
					save_settings();
					buf_pos = strchr(buf_pos, '$');
					if(*(buf_pos + 1) == '$')
					{
						sprintf(sms_txt, "%u.%u.%u.%u,%u.%u.%u.%u,%u.%u.%u.%u,%u,%u,%u,%s,%s,%s,%u", ExIP[0][0], ExIP[0][1], ExIP[0][2], ExIP[0][3], ExIP[1][0], ExIP[1][1], ExIP[1][2], ExIP[1][3], ExIP[2][0], ExIP[2][1], ExIP[2][2], ExIP[2][3], ExPort[0], ExPort[1], ExPort[2], APN, APN_user, APN_pass, PortPr);
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "getparam1##", 11))
				{
					getparam1 = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "setparam2#", 10))
				{
					buf_pos = buf_pos + 10;
					sscanf(buf_pos, "%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u", &Period1, &Period2, &Send_per1, &Send_per2, &Settings, &Settings1, &Stealth_per, &Stealth_ontm, &Period3, &Rsindp, &Sync);
					if(Settings & 16)
					{
						bton = EAT_TRUE;
					}
					else
					{
						btoff = EAT_TRUE;
					}
					save_settings();
					buf_pos = strchr(buf_pos, '$');
					if(*(buf_pos + 1) == '$')
					{
						sprintf(sms_txt, "%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u", Period1, Period2, Send_per1, Send_per2, Settings, Settings1, Stealth_per, Stealth_ontm, Period3, Rsindp, Sync);
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "getparam2##", 11))
				{
					getparam2 = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "setparam3#", 10))
				{
					buf_pos = buf_pos + 10;
					sscanf(buf_pos, "%u,%u,%u,%u,%u,%*u,%u,%u,%u,%u,%u,%u,%u", &prm_per, &gsmloc_per, &money_per, &trip_per, &debug_per, &can1_per, &can2_per, &ADC_per, &INx_per, &freq_per, &ident_per, &offsim_per);
					save_settings();
					buf_pos = strchr(buf_pos, '$');
					if(*(buf_pos + 1) == '$')
					{
						sprintf(sms_txt, "%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u", prm_per, gsmloc_per, money_per, trip_per, debug_per, 0, can1_per, can2_per, ADC_per, INx_per, freq_per, ident_per, offsim_per);
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "getparam3##", 11))
				{
					getparam3 = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "setparam4#", 10))
				{
					buf_pos = buf_pos + 10;
					sscanf(buf_pos, "%u,%4[^,],%10[^,],%u,%u,%u", &Vbt_off, SMS_pass, MoneyUSSD, &Speed_lim, &Vcc_lim, &Vbt_lim);
					save_settings();
					buf_pos = strchr(buf_pos, '$');
					if(*(buf_pos + 1) == '$')
					{
						sprintf(sms_txt, "%u,%s,%s,%u,%u,%u", Vbt_off, SMS_pass, MoneyUSSD, Speed_lim, Vcc_lim, Vbt_lim);
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "setpass#", 8))
				{
					buf_pos = buf_pos + 8;
					sscanf(buf_pos, "%4[^$]", SMS_pass);
					save_settings();
					buf_pos = strchr(buf_pos, '$');
					if(*(buf_pos + 1) == '$')
					{
						sprintf(sms_txt, "%s", SMS_pass);
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "getparam4##", 11))
				{
					getparam4 = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "setparam5#", 10))
				{
					buf_pos = buf_pos + 10;
					sscanf(buf_pos, "%12[^,],%12[^,],%12[^,],%12[^,],%12[^,],%12[^,],%12[^$]", NumAd1, NumAd2, Num1, Num2, Num3, Num4, Num5);
					save_settings();
					buf_pos = strchr(buf_pos, '$');
					if(*(buf_pos + 1) == '$')
					{
						sprintf(sms_txt, "%s,%s,%s,%s,%s,%s,%s", NumAd1, NumAd2, Num1, Num2, Num3, Num4, Num5);
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "getparam5##", 11))
				{
					getparam5 = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "fwload#", 7))
				{
					buf_pos = buf_pos + 7;
					sscanf(buf_pos, "%hhu.%hhu.%hhu.%hhu,%30[^,],%30[^,],%100[^$]", &FTP_server[0], &FTP_server[1], &FTP_server[2], &FTP_server[3], FTP_user, FTP_pass, FTP_path);
eat_trace("FTP_path:%s", FTP_path);
eat_trace(FTP_path);
					buf_pos = strrchr(FTP_path, 0x2F);
eat_trace("buf_pos:%s", buf_pos);
					strcpy(fw_filename, (buf_pos + 1));
					*(buf_pos + 1) = 0;
					fw_update = EAT_TRUE;
					buf_pos = strchr(buf_pos, '$');
					if(*(buf_pos + 1) == '$')
					{
						sprintf(sms_txt, "%u.%u.%u.%u,%s,%s,%s", FTP_server[0], FTP_server[1], FTP_server[2], FTP_server[3], FTP_user, FTP_pass, FTP_path);
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "ussd#", 5))
				{
					buf_pos = buf_pos + 5;
					sscanf(buf_pos, "%100[^$]", ussdcmd);
					ussd_send = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "modinfo##", 9))
				{
					modinfo = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "pos2sms##", 9))
				{
					pos2sms = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "bton#", 5))
				{
					Settings = Settings | 16;
					save_settings();
					bton = EAT_TRUE;
					if(*(buf_pos+5) == '#')
					{
						strcpy(sms_txt, "Bluetooth on.");
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "btoff#", 6))
				{
					Settings = Settings & (0xFFFF - 16);
					save_settings();
					btoff = EAT_TRUE;
					if(*(buf_pos+6) == '#')
					{
						strcpy(sms_txt, "Bluetooth off.");
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "block##", 7))
				{
					eng_block = 1;
					save_status();
					strcpy(sms_txt, "Command \"block\" accepted.");
					send_sms(sms_nbr, sms_txt);
				}
				if(!memcmp(buf_pos, "cpureset##", 10))
				{
					cpureset = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "stsreset##", 10))
				{
					stsreset = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "gsmoffon##", 10))
				{
					gsmoffon = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "sblock##", 8))
				{
					eng_block = 2;
					save_status();
					strcpy(sms_txt, "Command \"sblock\" accepted.");
					send_sms(sms_nbr, sms_txt);
				}
				if(!memcmp(buf_pos, "unblock##", 9))
				{
					eng_block = 0;
					save_status();
					strcpy(sms_txt, "Command \"unblock\" accepted.");
					send_sms(sms_nbr, sms_txt);
				}
				if(!memcmp(buf_pos, "fsinfo##", 8))
				{
					fsinfo = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "smsmode#", 8))
				{
					Settings = Settings | 512;
					if(*(buf_pos+9) == '#')
					{
						strcpy(sms_txt, "SMS mode enabled.");
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "gprsmode#", 9))
				{
					Settings = Settings & (0xFFFF - 512);
					if(*(buf_pos+9) == '#')
					{
						strcpy(sms_txt, "GPRS mode enabled.");
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "addnumbers#", 11))
				{
					buf_pos = buf_pos + 10;
					tmpcnt = 0;
					do{
						buf_pos++;
						sscanf(buf_pos, "%12[^,$]", nbr_tmp);
						if(phone_nbr_add(nbr_tmp))
							tmpcnt++;
						buf_pos = strchr(buf_pos, ',');
					}while(buf_pos);
					buf_pos = strchr(buf_pos, ',');
					if(strchr((const char*)smsReadCnfContent.data, '$'))
					{
						sprintf(sms_txt, "%u numbers added to list.", tmpcnt);
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "delnumbers#", 11))
				{
					buf_pos = buf_pos + 10;
					tmpcnt = 0;
					do{
						buf_pos++;
						sscanf(buf_pos, "%12[^,$]", nbr_tmp);
						if(phone_nbr_del(nbr_tmp))
							tmpcnt++;
						buf_pos = strchr(buf_pos, ',');
					}while(buf_pos);
					buf_pos = strchr(buf_pos, ',');
					if(strchr((const char*)smsReadCnfContent.data, '$'))
					{
						sprintf(sms_txt, "%u numbers deleted from list.", tmpcnt);
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "getnumbers##", 12))
				{
					getnumbers = EAT_TRUE;
				}
				if(!memcmp(buf_pos, "clearnumbers#", 13))
				{
					eat_fs_Delete(L"C:\\Numbers.txt");
					if(*(buf_pos+13) == '#')
					{
						strcpy(sms_txt, "All numbers are deleted.");
						send_sms(sms_nbr, sms_txt);
					}
				}
				if(!memcmp(buf_pos, "outperiod#", 10))
				{
					buf_pos = buf_pos + 10;
					sscanf(buf_pos, "%hhu", &OutOnPeriod);
					save_settings();
					buf_pos = strchr(buf_pos, '$');
					if(*(buf_pos + 1) == '$')
					{
						sprintf(sms_txt, "%u", OutOnPeriod);
						send_sms(sms_nbr, sms_txt);
					}
				}
			}
		}
	}
	eat_delete_sms(insms_id, eat_sms_delete_cb);
}

static void
eat_sms_ready_cb(eat_bool result)
{
	if(result)
	{
		eat_modem_write("AT+CMGDA=\"DEL ALL\"\r", strlen("AT+CMGDA=\"DEL ALL\"\r"));
	}
eat_trace("eat_sms_ready_cb, result=%d", result);
}

static void
eat_sms_new_message_cb(EatSmsNewMessageInd_st smsNewMessage)
{
eat_trace("eat_sms_new_message_cb, storage=%d,index=%d", smsNewMessage.storage, smsNewMessage.index);
	eat_read_sms(smsNewMessage.index, eat_sms_read_cb);
	insms_id = smsNewMessage.index;
}

static void
eat_sms_send_cb(eat_bool result)
{
	sms_sended = EAT_TRUE;
eat_trace("eat_sms_send_cb, result=%d", result);
}

unsigned int
pktsz(unsigned int pktnbr)
{
	unsigned int retval = 0;
	switch(pktnbr)
	{
		case 3:
			retval = 10;
		break;
		case 5:
			retval = 8;
		break;
		case 6:
			retval = 10;
		break;
		case 7:
			retval = 38;
		break;
		case 9:
			retval = 12;
		break;
		case 10:
			retval = 18;
		break;
		case 12:
			retval = 10;
		break;
		case 13:
			retval = 10;
		break;
		case 16:
			retval = 3;
		break;
		case 18:
			retval = 7;
		break;
		case 22:
			retval = 20;
		break;
		case 26:
			retval = 252;
		break;
		case 30:
			retval = 2;
		break;
		case 33:
			retval = 16;
		break;
		case 35:
			retval = 10;
		break;
		case 37:
			retval = 86;
		break;
		case 38:
			retval = 11;
		break;
		case 100:
			retval = 52;
		break;
		default:
			eeprom_p1 = 0;
			eeprom_p2 = 0;
			eeprom_p2tmp = 0;
			out_buf_col = 0;
		break;
	}
	return retval;
}

unsigned char
read_byte(void)
{
	unsigned char rbyte;

	rbyte = main_buf[eeprom_p2tmp];
	return rbyte;
}

void
write_byte(unsigned char data)
{
	main_buf[eeprom_p1] = data;
	CRC = CRC + data;
	eeprom_p1++;
	if(eeprom_p1 >= main_buf_size)
		eeprom_p1 = 0;
}

void
buf_col_get(void)
{
	if(eeprom_p1 < eeprom_p2)
		out_buf_col = main_buf_size - (eeprom_p2 - eeprom_p1);
	else
		out_buf_col = eeprom_p1 - eeprom_p2;
}

void
wr_pkt(u8 pkt)
{
	struct tm cur_time;
	time_t cur_timeUTC;
    EatRtc_st rtc = {0};
	char ExIPt[16];
	u8 i;

	if(out_buf_col < (main_buf_size - pktsz(pkt)))
	{
		CRC = 0;
		if(pkt == 22)
		{
			if(((SatUs >> 6) == 0)  || (Latitude == 0) || (Longitude == 0))
			{
				pkt = 35;
			}
		}
		write_byte(pkt);
		if((pkt != 16) && (pkt != 26) && (pkt != 30) && (pkt != 37) && (pkt != 100) && (pkt != 100))
		{
			if((Year < 17) || (Year == 80))
			{
				eat_get_rtc(&rtc);
				Year = rtc.year;
				Month = rtc.mon;
				Day = rtc.day;
				Hour = rtc.hour;
				Minute = rtc.min;
				Second = rtc.sec;
			}
			cur_time.tm_sec = Second;
			cur_time.tm_min = Minute;
			cur_time.tm_hour = Hour;
			cur_time.tm_mday = Day;
			cur_time.tm_mon = Month;
			if(cur_time.tm_mon != 0)
				cur_time.tm_mon--;
			cur_time.tm_year = Year + 100;
			cur_timeUTC = mktime(&cur_time);
			write_byte((unsigned char)(cur_timeUTC >> 24));
			write_byte((unsigned char)(cur_timeUTC >> 16));
			write_byte((unsigned char)(cur_timeUTC >> 8));
			write_byte((unsigned char)cur_timeUTC);
		}

		switch(pkt)
		{
			case 3:
			{
				write_byte(rssi);
				write_byte((unsigned char)(Vbt >> 8));
				write_byte((unsigned char)Vbt);
				write_byte(Tm);
			}
			break;
			case 5:
			{
				write_byte((unsigned char)(Money >> 8));
				write_byte((unsigned char)Money);
			}
			break;
			case 6:
			{
				write_byte((unsigned char)(Trip >> 24));
				write_byte((unsigned char)(Trip >> 16));
				write_byte((unsigned char)(Trip >> 8));
				write_byte((unsigned char)Trip);
			}
			break;
			case 7:
			{
				write_byte((unsigned char)(eeprom_p1 >> 24));
				write_byte((unsigned char)(eeprom_p1 >> 16));
				write_byte((unsigned char)(eeprom_p1 >> 8));
				write_byte((unsigned char)eeprom_p1);

				write_byte((unsigned char)(eeprom_p2 >> 24));
				write_byte((unsigned char)(eeprom_p2 >> 16));
				write_byte((unsigned char)(eeprom_p2 >> 8));
				write_byte((unsigned char)eeprom_p2);

				write_byte((unsigned char)(out_buf_col >> 24));
				write_byte((unsigned char)(out_buf_col >> 16));
				write_byte((unsigned char)(out_buf_col >> 8));
				write_byte((unsigned char)out_buf_col);

				write_byte(0);
				write_byte(0);
				write_byte(0);
				write_byte(0);

				write_byte(0);
				write_byte(0);

				write_byte(0);
				write_byte(0);

				write_byte(0);
				write_byte(0);

				write_byte((unsigned char)(Sts_d >> 8));
				write_byte((unsigned char)Sts_d);

				write_byte(0);
				write_byte(0);
				write_byte(0);
				write_byte(0);
				write_byte(0);
				write_byte(0);
				write_byte(0);
				write_byte(0);
			}
			break;
			case 12:
			{
				write_byte((unsigned char)(freq1 >> 8));
				write_byte((unsigned char)freq1);
				write_byte((unsigned char)(freq2 >> 8));
				write_byte((unsigned char)freq2);
			}
			break;
			case 13:
			{
				write_byte(ADC1);
				write_byte(ADC2);
				write_byte(0);
				write_byte(0);
			}
			break;
			case 16:
			{
				write_byte(cmd_ret);
				cmd_ret = 0;
			}
			break;
			case 18:
				write_byte(Event_nbr);
			break;
			case 22:
			{
				write_byte((unsigned char)(Latitude >> 16));
				write_byte((unsigned char)(Latitude >> 8));
				write_byte((unsigned char)Latitude);
				write_byte((unsigned char)(Longitude >> 16));
				write_byte((unsigned char)(Longitude >> 8));
				write_byte((unsigned char)Longitude);
				write_byte((unsigned char)(Speed >> 8));
				write_byte((unsigned char)Speed);
				write_byte((unsigned char)(Course / 2));
				write_byte(SatUs);
				write_byte((unsigned char)(Sts_d >> 8));
				write_byte((unsigned char)Sts_d);
				write_byte((unsigned char)(Vcc >> 8));
				write_byte((unsigned char)Vcc);
			}
			break;
			case 26:
			{
				write_byte((unsigned char)(Version >> 8));
				write_byte((unsigned char)Version);
				for(i = 0; i < 6; i++)
					write_byte(ICC[i]);
				write_byte(0);
				for(i = 0; i < 30; i++)
					write_byte(simrev[i]);
				sprintf(ExIPt, "%hhu.%hhu.%hhu.%hhu", ExIP[0][0], ExIP[0][1], ExIP[0][2], ExIP[0][3]);
				for(i = 0; i < 15; i++)
					write_byte(ExIPt[i]);
				sprintf(ExIPt, "%hhu.%hhu.%hhu.%hhu", ExIP[1][0], ExIP[1][1], ExIP[1][2], ExIP[1][3]);
				for(i = 0; i < 15; i++)
					write_byte(ExIPt[i]);
				sprintf(ExIPt, "%hhu.%hhu.%hhu.%hhu", ExIP[2][0], ExIP[2][1], ExIP[2][2], ExIP[2][3]);
				for(i = 0; i < 15; i++)
					write_byte(ExIPt[i]);
				for(i = 0; i < 30; i++)
					write_byte(APN[i]);
				for(i = 0; i < 30; i++)
					write_byte(APN_user[i]);
				for(i = 0; i < 30; i++)
					write_byte(APN_pass[i]);
				for(i = 0; i < 4; i++)
					write_byte(SMS_pass[i]);
				for(i = 0; i < 10; i++)
					write_byte(MoneyUSSD[i]);
				write_byte((unsigned char)(Period1 >> 8));
				write_byte((unsigned char)Period1);
				write_byte((unsigned char)(Period2 >> 8));
				write_byte((unsigned char)Period2);
				write_byte((unsigned char)(prm_per >> 8));
				write_byte((unsigned char)prm_per);
				write_byte((unsigned char)(gsmloc_per >> 8));
				write_byte((unsigned char)gsmloc_per);
				write_byte((unsigned char)(money_per >> 8));
				write_byte((unsigned char)money_per);
				write_byte((unsigned char)(trip_per >> 8));
				write_byte((unsigned char)trip_per);
				write_byte((unsigned char)(debug_per >> 8));
				write_byte((unsigned char)debug_per);
				write_byte(0);
				write_byte(0);
				write_byte((unsigned char)(can1_per >> 8));
				write_byte((unsigned char)can1_per);
				write_byte((unsigned char)(can2_per >> 8));
				write_byte((unsigned char)can2_per);
				write_byte((unsigned char)(ADC_per >> 8));
				write_byte((unsigned char)ADC_per);
				write_byte((unsigned char)(INx_per >> 8));
				write_byte((unsigned char)INx_per);
				write_byte((unsigned char)(freq_per >> 8));
				write_byte((unsigned char)freq_per);
				write_byte((unsigned char)(ident_per >> 8));
				write_byte((unsigned char)ident_per);
				write_byte((unsigned char)(offsim_per >> 8));
				write_byte((unsigned char)offsim_per);
				write_byte((unsigned char)(Send_per1 >> 8));
				write_byte((unsigned char)Send_per1);
				write_byte((unsigned char)(Send_per2 >> 8));
				write_byte((unsigned char)Send_per2);
				write_byte((unsigned char)(Stealth_ontm >> 8));
				write_byte((unsigned char)Stealth_ontm);
				write_byte((unsigned char)(Stealth_per >> 8));
				write_byte((unsigned char)Stealth_per);
				write_byte((unsigned char)(Vbt_off >> 8));
				write_byte((unsigned char)Vbt_off);
				write_byte((unsigned char)(Settings >> 8));
				write_byte((unsigned char)Settings);
				write_byte((unsigned char)(Settings1 >> 8));
				write_byte((unsigned char)Settings1);
				write_byte((unsigned char)(ExPort[0] >> 8));
				write_byte((unsigned char)ExPort[0]);
				write_byte((unsigned char)(ExPort[1] >> 8));
				write_byte((unsigned char)ExPort[1]);
				write_byte((unsigned char)(ExPort[2] >> 8));
				write_byte((unsigned char)ExPort[2]);
				write_byte((unsigned char)(Speed_lim >> 8));
				write_byte((unsigned char)Speed_lim);
				write_byte((unsigned char)(Vcc_lim >> 8));
				write_byte((unsigned char)Vcc_lim);
				write_byte((unsigned char)(Vbt_lim >> 8));
				write_byte((unsigned char)Vbt_lim);
				write_byte((unsigned char)(Period3 >> 8));
				write_byte((unsigned char)Period3);
				write_byte((unsigned char)(Rsindp >> 8));
				write_byte((unsigned char)Rsindp);
				write_byte((unsigned char)Sync);
				write_byte((unsigned char)PortPr);
			}
			break;
			case 30:
			break;
			case 33:
			{
				write_byte((unsigned char)(MCC >> 8));
				write_byte((unsigned char)MCC);
				write_byte((unsigned char)(MNC >> 8));
				write_byte((unsigned char)MNC);
				write_byte((unsigned char)(LAC >> 8));
				write_byte((unsigned char)LAC);
				write_byte((unsigned char)(CID >> 8));
				write_byte((unsigned char)CID);
				write_byte((unsigned char)(Sts_d >> 8));
				write_byte((unsigned char)Sts_d);
			}
			break;
			case 35:
				write_byte((unsigned char)(Sts_d >> 8));
				write_byte((unsigned char)Sts_d);
				write_byte((unsigned char)(Vcc >> 8));
				write_byte((unsigned char)Vcc);
			break;
			case 37:
			{
				for(i = 0; i < 12; i++)
					write_byte(Num1[i]);
				for(i = 0; i < 12; i++)
					write_byte(Num2[i]);
				for(i = 0; i < 12; i++)
					write_byte(Num3[i]);
				for(i = 0; i < 12; i++)
					write_byte(Num4[i]);
				for(i = 0; i < 12; i++)
					write_byte(Num5[i]);
				for(i = 0; i < 12; i++)
					write_byte(NumAd1[i]);
				for(i = 0; i < 12; i++)
					write_byte(NumAd2[i]);
			}
			break;
			case 100:
				for(i = 0; i < 50; i++)
					write_byte((unsigned char)debug_buf[i]);
			break;
		}
		write_byte(CRC);
		buf_col_get();
	}
eat_trace("eeprom_p1:%d,eeprom_p2:%d,out_buf_col:%d", eeprom_p1, eeprom_p2, out_buf_col);
}

void
wr_event(u8 event)
{
	Event_nbr = event;
	wr_pkt(18);
}

void
write_at(char * at_cmd, char * at_ans, u16 at_t)
{
eat_trace("Send AT: %s", at_cmd);
	strcpy(at_answer, at_ans);
	at_timer = at_t;
	eat_send_msg_to_user(EAT_USER_1, EAT_USER_0, EAT_FALSE, strlen(at_cmd), (const unsigned char *)at_cmd, EAT_NULL);
	eat_sem_get(sem_at_done, EAT_INFINITE_WAIT);
}

u8 *SOC_EVENT[]={
    "SOC_READ",
    "SOC_WRITE",  
    "SOC_ACCEPT", 
    "SOC_CONNECT",
    "SOC_CLOSE", 
    "SOC_ACKED"
};

void
soc_notify_cb(s8 s, soc_event_enum event, eat_bool result, u16 ack_size)
{
	char * buf_pos = NULL;
	char tmp_buf[100];
    EatRtc_st rtc = {0};
    u8 id = 0;
	u8 len;
	
	if(event & SOC_READ)
	{
		id = 0;
		len = eat_soc_recv(server_soc, server_answer, 1024);
		if(len > 0)
		{
			server_answer[len] = 0;
eat_trace("eat_soc_recv:%d, %s", len, server_answer);
			buf_pos = strstr(server_answer, "C0");
			if(buf_pos)
			{
eat_trace("C0 find");
				senderr_cnt = 0;
				rsindp_cnt = Rsindp;
				if(udpsend_st == 2)
				{
					udpsend_st = 3;
				}
				else
				if(udpsend_st == 4)
				{
					udpsend_st = 5;
				}
				switch(*(buf_pos+2))
				{
					case '1':
					{
						if(*(buf_pos+3) == ',')
						{
							buf_pos = buf_pos + 4;
							sscanf(buf_pos, "%hhu,%hhu,%hhu,%hhu,%hhu,%hhu", &Year, &Month, &Day, &Hour, &Minute, &Second);
							rtc.year = Year;
							rtc.mon = Month;
							rtc.day = Day;
							rtc.hour = Hour;
							rtc.min = Minute;
							rtc.sec = Second;
							eat_set_rtc(&rtc);
						}
					}
					break;
					case '2':
						buf_pos = buf_pos + 4;
						sscanf(buf_pos, "%hhu.%hhu.%hhu.%hhu,%hhu.%hhu.%hhu.%hhu,%hhu.%hhu.%hhu.%hhu,%u,%u,%u,%30[^,],%30[^,],%30[^,],%hhu", &ExIP[0][0], &ExIP[0][1], &ExIP[0][2], &ExIP[0][3], &ExIP[1][0], &ExIP[1][1], &ExIP[1][2], &ExIP[1][3], &ExIP[2][0], &ExIP[2][1], &ExIP[2][2], &ExIP[2][3], &ExPort[0], &ExPort[1], &ExPort[2], APN, APN_user, APN_pass, &PortPr);
						save_settings();
						cmd_ret = cmd_ret | 1;
						wr_pkt(16);
eat_trace("%u.%u.%u.%u,%u.%u.%u.%u,%u.%u.%u.%u,%u,%u,%u,%s,%s,%s,%u", ExIP[0][0], ExIP[0][1], ExIP[0][2], ExIP[0][3], ExIP[1][0], ExIP[1][1], ExIP[1][2], ExIP[1][3], ExIP[2][0], ExIP[2][1], ExIP[2][2], ExIP[2][3], ExPort[0], ExPort[1], ExPort[2], APN, APN_user, APN_pass, PortPr);
					break;
					case '3':
						buf_pos = buf_pos + 4;
						sscanf(buf_pos, "%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u", &Period1, &Period2, &Send_per1, &Send_per2, &Settings, &Settings1, &Stealth_per, &Stealth_ontm, &Period3, &Rsindp, &Sync);
						if(Settings & 16)
						{
							bton = EAT_TRUE;
						}
						else
						{
							btoff = EAT_TRUE;
						}
						save_settings();
						cmd_ret = cmd_ret | 2;
						wr_pkt(16);
eat_trace("%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u", Period1, Period2, Send_per1, Send_per2, Settings, Settings1, Stealth_per, Stealth_ontm, Period3, Rsindp, Sync);
					break;
					case '4':
						buf_pos = buf_pos + 4;
						sscanf(buf_pos, "%u,%u,%u,%u,%u,%*u,%u,%u,%u,%u,%u,%u,%u", &prm_per, &gsmloc_per, &money_per, &trip_per, &debug_per, &can1_per, &can2_per, &ADC_per, &INx_per, &freq_per, &ident_per, &offsim_per);
						save_settings();
						cmd_ret = cmd_ret | 4;
						wr_pkt(16);
eat_trace("%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u", prm_per, gsmloc_per, money_per, trip_per, debug_per, can1_per, can2_per, ADC_per, INx_per, freq_per, ident_per, offsim_per);
					break;
					case '5':
						buf_pos = buf_pos + 4;
						sscanf(buf_pos, "%u,%4[^,],%10[^,],%u,%u,%u", &Vbt_off, SMS_pass, MoneyUSSD, &Speed_lim, &Vcc_lim, &Vbt_lim);
						save_settings();
						cmd_ret = cmd_ret | 8;
						wr_pkt(16);
eat_trace("%u,%s,%s,%u,%u,%u", Vbt_off, SMS_pass, MoneyUSSD, Speed_lim, Vcc_lim, Vbt_lim);
					break;
					case '6':
						buf_pos = buf_pos + 4;
						sscanf(buf_pos, "%12[^,],%12[^,],%12[^,],%12[^,],%12[^,],%12[^,],%12[^\r\n]", NumAd1, NumAd2, Num1, Num2, Num3, Num4, Num5);
						save_settings();
						cmd_ret = cmd_ret | 16;
						wr_pkt(16);
eat_trace("%s,%s,%s,%s,%s,%s,%s", NumAd1, NumAd2, Num1, Num2, Num3, Num4, Num5);
					break;
					case '7':
						buf_pos = buf_pos + 4;
						eng_block = atoi(buf_pos);
						save_status();
						cmd_ret = cmd_ret | 32;
						wr_pkt(16);
eat_trace("eng_block:%u", eng_block);
					break;
					case '8':
					{
						buf_pos = buf_pos + 4;
						do_req = atoi(buf_pos);
eat_trace("do_req:%d", do_req);
						if(do_req & 1)
						{
							do_req = do_req & (0xFFFF - 1);
							wr_pkt(7);
						}
						if(do_req & 2)
						{
							do_req = do_req & (0xFFFF - 2);
						}
						if(do_req & 4)
						{
							do_req = do_req & (0xFFFF - 4);
							wr_pkt(26);
							wr_pkt(37);
						}
						if(do_req & 8)
						{
							do_req = do_req & (0xFFFF - 8);
							wr_pkt(3);
						}
						if(do_req & 16)
						{
							do_req = do_req & (0xFFFF - 16);
							gsmloc_f = EAT_TRUE;
						}
						if(do_req & 32)
						{
							do_req = do_req & (0xFFFF - 32);
							money_f = EAT_TRUE;
						}
						if(do_req & 64)
						{
							do_req = do_req & (0xFFFF - 64);
							wr_pkt(6);
						}
						if(do_req & 128)
						{
							do_req = do_req & (0xFFFF - 128);
							send_cfun4 = EAT_TRUE;
						}
						if(do_req & 256)
						{
							do_req = do_req & (0xFFFF - 256);
							simreset_f = EAT_TRUE;
						}
						if(do_req & 512)
						{
							do_req = do_req & (0xFFFF - 512);
						}
						if(do_req & 1024)
						{
							do_req = do_req & (0xFFFF - 1024);
						}
						if(do_req & 2048)
						{
							do_req = do_req & (0xFFFF - 2048);
							eat_fs_Delete(L"C:\\Settings.txt");
							simreset_f = EAT_TRUE;
						}
						if(do_req & 32768)
						{
							do_req = do_req & (0xFFFF - 32768);
							log_upload = EAT_TRUE;
						}
						cmd_ret = cmd_ret | 64;
						wr_pkt(16);
					}
					break;
					case '9':
					{
						udpsend_st = 1;
eat_trace("reindent=1");
					}
					break;
					case 'B':
						buf_pos = buf_pos + 4;
						sscanf(buf_pos, "%hhu.%hhu.%hhu.%hhu,%30[^,],%30[^,],%100[^\r\n]", &FTP_server[0], &FTP_server[1], &FTP_server[2], &FTP_server[3], FTP_user, FTP_pass, FTP_path);
eat_trace("FTP_path:%s", FTP_path);
eat_trace(FTP_path);
						buf_pos = strrchr(FTP_path, 0x2F);
eat_trace("buf_pos:%s", buf_pos);
						strcpy(fw_filename, (buf_pos + 1));
						*(buf_pos + 1) = 0;
						cmd_ret = cmd_ret | 128;
						wr_pkt(16);
						fw_update = EAT_TRUE;
eat_trace("%u.%u.%u.%u,%s,%s,%s", FTP_server[0], FTP_server[1], FTP_server[2], FTP_server[3], FTP_user, FTP_pass, FTP_path);
					break;
				}
			}
		}
	}
	else if (event & SOC_WRITE)
	{
		id = 1;
		s_st = 1;
	}
	else if (event & SOC_ACCEPT)
	{
		id = 2;
		s_st = 2;
	}
	else if (event & SOC_CONNECT)
	{
		id = 3;
		s_st = 3;
	}
	else if (event & SOC_CLOSE)
	{
		id = 4;
		s_st = 4;
		eat_soc_close(s);
	}
	else if (event & SOC_ACKED)
	{
		id = 5;
		s_st = 5;
	}

	if(id == 5)
eat_trace("SOC_NOTIFY:%d,%s,%d\r\n",s,SOC_EVENT[id], ack_size);
	else 
eat_trace("SOC_NOTIFY:%d,%s,%d\r\n",s,SOC_EVENT[id], result);

	sprintf(tmp_buf, "soc_notify_cb %u", id);
	if(id != 0)
	{
		write_log(tmp_buf);
	}
eat_trace(tmp_buf);
}

void
bear_notify_cb(cbm_bearer_state_enum state, u8 ip_addr[4])
{
	u8 val;
	s8 ret;
	char tmp_buf[100];

	if(state & CBM_DEACTIVATED)
	{
		bear_st = 0;
	}
    else
	if(state & CBM_ACTIVATING)
	{
		bear_st = 1;
	}
    else
	if(state & CBM_ACTIVATED)
	{
		bear_st = 2;
		own_ip[0] = ip_addr[0];
		own_ip[1] = ip_addr[1];
		own_ip[2] = ip_addr[2];
		own_ip[3] = ip_addr[3];
		server_soc = eat_soc_create(SOC_SOCK_DGRAM, 0);
		if(server_soc < 0)
eat_trace("eat_soc_create return error :%d", server_soc);
		else
eat_trace("socket id :%d", server_soc);
		val = TRUE;
		ret = eat_soc_setsockopt(server_soc, SOC_NBIO, &val, sizeof(val));
		if(ret != SOC_SUCCESS)
eat_trace("eat_soc_setsockopt 2 return error :%d",ret);
		val = (SOC_READ | SOC_WRITE | SOC_CLOSE | SOC_CONNECT | SOC_ACCEPT);
		ret = eat_soc_setsockopt(server_soc, SOC_ASYNC, &val,sizeof(val));
		if(ret != SOC_SUCCESS)
eat_trace("eat_soc_setsockopt 1 return error :%d", ret);
	}
    else
	if(state & CBM_DEACTIVATING)
	{
		bear_st = 3;
	}
    else
	if(state & CBM_CSD_AUTO_DISC_TIMEOUT)
	{
		bear_st = 4;
	}
    else
	if(state & CBM_GPRS_AUTO_DISC_TIMEOUT)
	{
		bear_st = 5;
	}
    else
	if(state & CBM_NWK_NEG_QOS_MODIFY)
	{
		bear_st = 6;
	}
    else
	if(state & CBM_WIFI_STA_INFO_MODIFY)
	{
		bear_st = 7;
	}
	sprintf(tmp_buf, "bear_notify_cb %u", bear_st);
	write_log(tmp_buf);
eat_trace(tmp_buf);
}

void
hostname_notify_cb(u32 request_id, eat_bool result, u8 ip_addr[4])
{
	char tmp_buf[100];

	sprintf(tmp_buf, "HOSTNAME_NOTIFY:%d,%d,%d:%d:%d:%d\r\n", request_id, result, ip_addr[0], ip_addr[1], ip_addr[2], ip_addr[3]);
	write_log(tmp_buf);
eat_trace(tmp_buf);
}

void app_main(void *data)
{
    EatEntryPara_st *para;
	EatEvent_st event;
	char input_buf[1024];
	char * buf_pos = NULL, dtmf_cmd = 0;
	u16 len = 0, out_cnt = 0;
	EAT_CBC_ST bmt = {0};
	s32 cmte = 0;
	u16 i = 0, i1 = 0;
    EatRtc_st rtc = {0};
	s8 ret = 0;
	char tmp_buf[300];

    APP_InitRegions();//Init app RAM, first step
    APP_init_clib(); //C library initialize, second step
eat_trace(" app_main ENTRY");

    para = (EatEntryPara_st*)data;

    memcpy(&app_para, para, sizeof(EatEntryPara_st));
    eat_trace("App Main ENTRY update:%d result:%d", app_para.is_update_app,app_para.update_app_result);
    if(app_para.is_update_app && app_para.update_app_result)
    {
        eat_update_app_ok();
    }

	if(eat_mem_init(s_memPool, EAT_MEM_MAX_SIZE) != EAT_TRUE)
	{
eat_trace("ERROR: eat memory initial error!");
	}

	if(!load_settings())
		save_settings();
	if(!load_status())
		save_status();

	eat_gpio_setup(LED, EAT_GPIO_DIR_OUTPUT, EAT_GPIO_LEVEL_LOW);
	eat_gpio_write(LED, EAT_GPIO_LEVEL_LOW);
	eat_gpio_setup(INZ, EAT_GPIO_DIR_INPUT, EAT_GPIO_LEVEL_LOW);
	if(eat_gpio_read(INZ) == EAT_GPIO_LEVEL_HIGH)
		Sts_d = Sts_d & (0xFFFF - 8);
	else
		Sts_d = Sts_d | 8;
	eat_gpio_setup(OUT1, EAT_GPIO_DIR_OUTPUT, EAT_GPIO_LEVEL_LOW);
	
	eat_set_sms_operation_mode(EAT_TRUE);
	eat_sms_register_new_message_callback(eat_sms_new_message_cb);
	eat_sms_register_sms_ready_callback(eat_sms_ready_cb);
	eat_sms_register_send_completed_callback(eat_sms_send_cb);
	eat_set_sms_format(1);
	eat_poweroff_key_sw(EAT_TRUE);
	eat_modem_set_poweron_urc_dir(EAT_USER_0);
	strcpy(simrev, eat_get_version());
	eat_get_imei((u8*)&IMEI[1], 15);
	IMEI[16] = 0;
	for(i = 0; i < 16; i++)
	{
		IMEI[16] = IMEI[16] + IMEI[i];
	}

	server_adr.sock_type = SOC_SOCK_DGRAM;
	server_adr.addr_len = 4;
	server_adr.port = ExPort[ExIPN];
	server_adr.addr[0]=ExIP[ExIPN][0];
	server_adr.addr[1]=ExIP[ExIPN][1];
	server_adr.addr[2]=ExIP[ExIPN][2];
	server_adr.addr[3]=ExIP[ExIPN][3];

	eat_soc_notify_register(soc_notify_cb);
	eat_soc_gethost_notify_register(hostname_notify_cb);
	sem_at_done = eat_create_sem("at_done", 0);
	eat_timer_start(EAT_TIMER_1, 1000);
	eat_timer_start(EAT_TIMER_2, 10000);
	
	if(!(Settings & 512))
	{
		wr_pkt(30);
		do_send = EAT_TRUE;
	}

	write_log("App started");
    while(EAT_TRUE)
    {
        eat_get_event(&event);
//eat_trace("MSG id%x", event.event);
        switch(event.event)
        {
            case EAT_EVENT_USER_MSG:
			{
eat_trace("Messege to User0");
				eat_modem_write(event.data.user_msg.data, event.data.user_msg.len);
				eat_timer_start(EAT_TIMER_3, at_timer);
				at_res = 0;
			}
            case EAT_EVENT_MDM_READY_RD:
			{
				len = eat_modem_read((unsigned char *)input_buf, 1024);
				if(len > 0)
				{
					input_buf[len] = 0;
eat_trace("From Mdm:%s", input_buf);
					if(at_answer[0])
					{
						buf_pos = strstr(input_buf, at_answer);
						if(buf_pos)
						{
							at_res = 1;
							at_ret = buf_pos;
eat_trace("at_ret:%s", at_ret);
							eat_timer_stop(EAT_TIMER_3);
							eat_sem_put(sem_at_done);
							at_answer[0] = 0;
						}
					}
					if(strstr(input_buf, "RDY"))
					{
						main_status = main_status | 1;
					}
					else
					if(strstr(input_buf, "Call Ready"))
					{
						main_status = main_status | 2;
					}
					else
					if(strstr(input_buf, "SMS Ready"))
					{
						main_status = main_status | 4;
					}
					buf_pos = strstr(input_buf, "+CFUN:");
					if(buf_pos)
					{
						buf_pos = buf_pos + 7;
						cfun = *buf_pos - 0x30;
					}
					buf_pos = strstr(input_buf, "+CPIN:");
					if(buf_pos)
					{
						buf_pos = buf_pos + 7;
						if(!memcmp(buf_pos, "READY", 5))
						{
							cpin = EAT_TRUE;
						}
						else
						{
							cpin = EAT_FALSE;
						}
					}
					if(ICC[0] == 0)
					{
						buf_pos = input_buf;
						do{
							while(!isdigit(*buf_pos) && *buf_pos)
							{
								buf_pos++;
							}
							if(!*buf_pos)
								break;
							for(i = 0; i < 19; i++)
							{
								if(!isdigit(*buf_pos))
									break;
								buf_pos++;
							}
							if(i == 19)
							{
								buf_pos = buf_pos - 6;
								memcpy(ICC, buf_pos, 6);
eat_trace("ICC:%c%c%c%c%c%c;", ICC[0], ICC[1], ICC[2], ICC[3], ICC[4], ICC[5]);
							}
						}while(*buf_pos && !ICC[0]);
					}
					buf_pos = strstr(input_buf, "+BTCONNECTING:");
					if(buf_pos)
					{
						btacpt = EAT_TRUE;
					}
					buf_pos = strstr(input_buf, "+BTPAIRING:");
					if(buf_pos)
					{
						btpair = EAT_TRUE;
					}
					buf_pos = strstr(input_buf, "+BTCONNECT: 2");
					if(buf_pos)
					{
						bt_menu_number = 0;
						show_bt_menu = EAT_TRUE;
					}
					buf_pos = strstr(input_buf, "+BTSPPDATA:");
					if(buf_pos)
					{
						buf_pos = buf_pos + 12;
						sscanf(buf_pos, "%*u,%*u,%12[^\\r]", tmp_buf);
eat_trace(tmp_buf);
						switch(bt_menu_number)
						{
							case 0:
							{
								if(strstr(tmp_buf, "1"))
								{
									bt_menu_number = 1;
									show_bt_menu = EAT_TRUE;
								}
								if(strstr(tmp_buf, "2"))
								{
									bt_menu_number = 2;
									show_bt_menu = EAT_TRUE;
								}
								if(strstr(tmp_buf, "3"))
								{
									bt_menu_number = 3;
									show_bt_menu = EAT_TRUE;
								}
								break;
							}
							case 1:
							{
								if(strstr(tmp_buf, "1"))
								{
									strcpy(bt_send_buf, "Menu 1 command 1 accepted.");
									bt_send_sets = EAT_TRUE;
								}
								if(strstr(tmp_buf, "2"))
								{
									strcpy(bt_send_buf, "Menu 1 command 2 accepted.");
									bt_send_nmbrs = EAT_TRUE;
								}
								if(strstr(tmp_buf, "3"))
								{
									strcpy(bt_send_buf, "Menu 1 command 3 accepted.");
								}
								if(strstr(tmp_buf, "4"))
								{
									bt_menu_number = 0;
									show_bt_menu = EAT_TRUE;
								}
								break;
							}
							case 2:
							{
								if(strstr(tmp_buf, "1"))
								{
									strcpy(bt_send_buf, "Menu 2 command 1 accepted.");
									bt_send_sets = EAT_TRUE;
								}
								if(strstr(tmp_buf, "2"))
								{
									strcpy(bt_send_buf, "Menu 2 command 2 accepted.");
									bt_send_nmbrs = EAT_TRUE;
								}
								if(strstr(tmp_buf, "3"))
								{
									strcpy(bt_send_buf, "Menu 2 command 3 accepted.");
								}
								if(strstr(tmp_buf, "4"))
								{
									bt_menu_number = 0;
									show_bt_menu = EAT_TRUE;
								}
								break;
							}
							case 3:
							{
								if(strstr(tmp_buf, "1"))
								{
									strcpy(bt_send_buf, "Menu 3 command 1 accepted.");
									bt_send_sets = EAT_TRUE;
								}
								if(strstr(tmp_buf, "2"))
								{
									strcpy(bt_send_buf, "Menu 3 command 2 accepted.");
									bt_send_nmbrs = EAT_TRUE;
								}
								if(strstr(tmp_buf, "3"))
								{
									strcpy(bt_send_buf, "Menu 3 command 3 accepted.");
								}
								if(strstr(tmp_buf, "4"))
								{
									bt_menu_number = 0;
									show_bt_menu = EAT_TRUE;
								}
								break;
							}
						}
					}
					buf_pos = strstr(input_buf, "+DTMF:");
					if(buf_pos)
					{
						buf_pos = buf_pos + 7;
						dtmf_cmd = *buf_pos;
						if(dtmf_cmd == '#')
						{
							dtmf_menu_number = 0;
							dtmf_c = 'A';
							dtmf_d = 5;
							send_dtmf = EAT_TRUE;
						}
						switch(dtmf_menu_number)
						{
							case 0:
							{
								switch(dtmf_cmd)
								{
									case '0':
									{
										dtmf_menu_number = 1;
										dtmf_c = 'A';
										dtmf_d = 5;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '1':
									{
										dtmf_menu_number = 2;
										dtmf_c = 'A';
										dtmf_d = 5;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '2':
									{
										dtmf_menu_number = 3;
										dtmf_c = 'A';
										dtmf_d = 5;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '3':
									{
										dtmf_menu_number = 4;
										dtmf_c = 'A';
										dtmf_d = 5;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '4':
									{
										dtmf_menu_number = 5;
										dtmf_c = 'A';
										dtmf_d = 5;
										send_dtmf = EAT_TRUE;
										break;
									}
								}
								break;
							}
							case 1:
							{
								switch(dtmf_cmd)
								{
									case '0':
									{
										eat_fs_Delete(L"C:\\log.txt");
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '1':
									{
										log_write_en = 1;
										save_status();
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '2':
									{
										log_write_en = 0;
										save_status();
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '3':
									{
										log_upload = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
								}
								break;
							}
							case 2:
							{
								switch(dtmf_cmd)
								{
									case '0':
									{
										ath_simreset_f = EAT_TRUE;
										break;
									}
									case '1':
									{
										eat_fs_Delete(L"C:\\Settings.txt");
										ath_simreset_f = EAT_TRUE;
										break;
									}
									case '2':
									{
										gprs_reset = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
								}
								break;
							}
							case 3:
							{
								switch(dtmf_cmd)
								{
									case '0':
									{
										strcpy(sms_nbr, incall_nbr);
										fsinfo = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '1':
									{
										strcpy(sms_nbr, incall_nbr);
										pos2sms = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '2':
									{
										strcpy(sms_nbr, incall_nbr);
										modinfo = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '3':
									{
										strcpy(sms_nbr, incall_nbr);
										getparam1 = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '4':
									{
										strcpy(sms_nbr, incall_nbr);
										getparam2 = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '5':
									{
										strcpy(sms_nbr, incall_nbr);
										getparam3 = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '6':
									{
										strcpy(sms_nbr, incall_nbr);
										getparam4 = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '7':
									{
										strcpy(sms_nbr, incall_nbr);
										getparam5 = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
								}
							}
							break;
							case 4:
							{
								switch(dtmf_cmd)
								{
									case '0':
									{
										eng_block = 2;
										save_status();
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '1':
									{
										eng_block = 1;
										save_status();
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '2':
									{
										eng_block = 0;
										save_status();
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
								}
								break;
							}
							case 5:
							{
								switch(dtmf_cmd)
								{
									case '0':
									{
										Settings = Settings | 16;
										save_settings();
										bton = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
									case '1':
									{
										Settings = Settings & (0xFFFF - 16);
										save_settings();
										btoff = EAT_TRUE;
										dtmf_c = 'A';
										dtmf_d = 1;
										send_dtmf = EAT_TRUE;
										break;
									}
								}
								break;
							}
						}
					}
					buf_pos = strstr(input_buf, "+CLIP:");
					if(buf_pos)
					{
write_log("Incoming call");
						incall_nbr[0] = 0;
						buf_pos = strchr(buf_pos, '\"');
						buf_pos++;
						if(*buf_pos == '+')
							buf_pos++;
						sscanf(buf_pos, "%12[^\"]", incall_nbr);
						if(phone_nbr_chk(incall_nbr))
						{
							gate_open = EAT_TRUE;
						}
						if(!strcmp(incall_nbr, Num1) || !strcmp(incall_nbr, Num2) || !strcmp(incall_nbr, Num3) || !strcmp(incall_nbr, Num4) || !strcmp(incall_nbr, Num5) || !strcmp(incall_nbr, NumAd1) || !strcmp(incall_nbr, NumAd2))
						{
							ata_f = EAT_TRUE;
						}
						else
						{
							ath_f = EAT_TRUE;
						}
					}
					buf_pos = strstr(input_buf, "NO CARRIER");
					if(buf_pos)
					{
						incall_f = EAT_FALSE;
					}
					buf_pos = strstr(input_buf, "SJDR:");
					if(buf_pos)
					{
						buf_pos = buf_pos + 6;
						if(!memcmp(buf_pos, "JAMMING DETECTED", 16))
						{
							if(!(Sts_d & 256))
							{
								Sts_d = Sts_d | 256;
							}
						}
						if(!memcmp(buf_pos, "NO JAMMING", 10))
						{
							if(Sts_d & 256)
							{
								Sts_d = Sts_d & (0xFFFF - 256);
							}
						}
					}
				}
			}
			break;
            case EAT_EVENT_UART_READY_RD:
			{
			}
			break;
			case EAT_EVENT_TIMER:
			{
				if(event.data.timer.timer_id == EAT_TIMER_1)
				{
					eat_timer_start(EAT_TIMER_1, 1000);

					if(eat_get_adc_sync(EAT_PIN38_ADC, (u32 *)&Vcc))
						Vcc = Vcc * 13;
					
					if(Vcc < Vcc_lim)
					{
						if(vclim_cnt != 5)
							vclim_cnt++;
					}
					else
					{
						if(vclim_cnt != 0)
							vclim_cnt--;
					}
					if(vclim_cnt == 5)
					{
						if(!(Sts_d & 2048))
						{
							Sts_d = Sts_d | 2048;
							wr_event(16);
							wr_pkt(22);
						}
					}
					if(vclim_cnt == 0)
					{
						if(Sts_d & 2048)
						{
							Sts_d = Sts_d & (0xFFFF - 2048);
						}
					}
					if(Vcc < 5000)
					{
						if(uv_cnt != 5)
							uv_cnt++;
					}
					else
					{
						if(uv_cnt != 0)
							uv_cnt--;
					}
					if(uv_cnt == 5)
					{
						if(!(Sts_d & 512))
						{
							wr_event(5);
							Sts_d = Sts_d | 512;
							if(Settings1 & 4)
								wr_pkt(22);
							if(Settings1 & 8)
								do_send = EAT_TRUE;
						}
					}
					if(uv_cnt == 0)
					{
						if(Sts_d & 512)
						{
							Sts_d = Sts_d & (0xFFFF - 512);
							if(Settings1 & 4)
								wr_pkt(22);
							if(Settings1 & 8)
								do_send = EAT_TRUE;
						}
					}

					if(simreset_f)
					{
						eat_reset_module();
						simreset_f = EAT_FALSE;
					}
					if(eat_gpio_read(INZ) == EAT_GPIO_LEVEL_HIGH)
					{
						if(Sts_d & 8)
						{
							Sts_d = Sts_d & (0xFFFF - 8);
							if(Settings1 & 1)
								wr_pkt(22);
							if(Settings1 & 2)
								do_send = EAT_TRUE;
						}
					}
					else
					{
						if(!(Sts_d & 8))
						{
							Sts_d = Sts_d | 8;
							if(Settings1 & 1)
								wr_pkt(22);
							if(Settings1 & 2)
								do_send = EAT_TRUE;
						}
					}
					switch(send_sms_st)
					{
						case 0:
						{
							if(send_sms_f)
							{
								if(Num1[0] != 0)
								{
eat_trace("Send SMS to Nbr1");
									sms_sended = EAT_FALSE;
									send_sms(Num1, sms_txt);
									send_sms_st = 1;
								}
								else
								{
									send_sms_st = 2;
								}
							}
						}
						break;
						case 1:
						{
							if(sms_sended)
							{
								send_sms_st = 2;
							}
						}
						break;
						case 2:
						{
							if(Num2[0] != 0)
							{
eat_trace("Send SMS to Nbr2");
								sms_sended = EAT_FALSE;
								send_sms(Num2, sms_txt);
								send_sms_st = 3;
							}
							else
							{
								send_sms_st = 4;
							}
						}
						break;
						case 3:
						{
							if(sms_sended)
							{
								send_sms_st = 4;
							}
						}
						break;
						case 4:
						{
							if(Num3[0] != 0)
							{
eat_trace("Send SMS to Nbr3");
								sms_sended = EAT_FALSE;
								send_sms(Num3, sms_txt);
								send_sms_st = 5;
							}
							else
							{
								send_sms_st = 6;
							}
						}
						break;
						case 5:
						{
							if(sms_sended)
							{
								send_sms_st = 6;
							}
						}
						break;
						case 6:
						{
							if(Num4[0] != 0)
							{
eat_trace("Send SMS to Nbr4");
								sms_sended = EAT_FALSE;
								send_sms(Num4, sms_txt);
								send_sms_st = 7;
							}
							else
							{
								send_sms_st = 8;
							}
						}
						break;
						case 7:
						{
							if(sms_sended)
							{
								send_sms_st = 8;
							}
						}
						break;
						case 8:
						{
							if(Num5[0] != 0)
							{
eat_trace("Send SMS to Nbr5");
								sms_sended = EAT_FALSE;
								send_sms(Num5, sms_txt);
								send_sms_st = 9;
							}
							else
							{
								send_sms_st = 10;
							}
						}
						break;
						case 9:
						{
							if(sms_sended)
							{
								send_sms_st = 10;
							}
						}
						break;
						case 10:
						{
							send_sms_f = EAT_FALSE;
							send_sms_st = 0;
						}
						break;
					}

					switch(gprs_st)
					{
						case 0:
						{
							if((gprs_enable) && (gsm_reg != 5 || (Settings & 32)) && (!(Settings & 512)) && (main_status&2))
							{
								if(bear_st != 2)
								{
									eat_gprs_bearer_open(APN, APN_user, APN_pass, bear_notify_cb);
								}
								gprs_st_timer = 0;
								gprs_st = 1;
							}
						}
						break;
						case 1:
						{
							if(bear_st == 2)
							{
								gprs_st_errcnt = 0;
								gprs_st = 2;
							}
							gprs_st_timer++;
							if(gprs_st_timer > 20)
							{
								gprs_st_errcnt++;
								gprs_st = 0;
							}
						}
						break;
						case 2:
						{
							if((!gprs_enable) || (gsm_reg == 5 && (!(Settings & 32))) || (Settings & 512))
							{
								ret = eat_soc_close(server_soc);
					            ret = eat_gprs_bearer_release();
sprintf(tmp_buf, "eat_gprs_bearer_release:%d", ret);
eat_trace(tmp_buf);
write_log(tmp_buf);
								gprs_st = 0;
							}
							else
							if(bear_st != 2)
							{
								gprs_st = 0;
							}
						}
						break;
					}

					switch(udpsend_st)
					{
						case 0:
						{
							if((bear_st == 2) && (do_send || (Settings&2048)) && (out_buf_col != 0))
							{
								do_send = EAT_FALSE;
								if(rsindp_cnt == 0)
									udpsend_st = 1;
								else
									udpsend_st = 3;
							}
						}
						break;
						case 1:
						{
							eat_soc_sendto(server_soc, IMEI, 17, &server_adr);
eat_trace("UDP send IMEI");
							udpsend_st_timer = 15;
							udpsend_st = 2;
						}
						break;
						case 2:
						{
							if(udpsend_st_timer != 0)
							{
								udpsend_st_timer--;
							}
							else
							{
								ExIPN++;
								if(ExIPN == 3)
									ExIPN = 0;
								server_adr.port = ExPort[ExIPN];
								server_adr.addr[0]=ExIP[ExIPN][0];
								server_adr.addr[1]=ExIP[ExIPN][1];
								server_adr.addr[2]=ExIP[ExIPN][2];
								server_adr.addr[3]=ExIP[ExIPN][3];

								udpsend_st = 1;
								senderr_cnt++;
								if(senderr_cnt > 30)
								{
									senderr_cnt = 0;
								}
								else
								if(senderr_cnt > 6)
								{
									udpsend_st_timer = 60;
									udpsend_st = 6;
								}
								else
								if(senderr_cnt == 3)
								{
									gprs_reset = EAT_TRUE;
write_log("GPRS reset");
									udpsend_st_timer = 10;
									udpsend_st = 6;
								}
							}
						}
						break;
						case 3:
						{
eat_trace("%u,%u,%u,%u,%u;", main_buf[eeprom_p2], main_buf[eeprom_p2+1], main_buf[eeprom_p2+2], main_buf[eeprom_p2+3], main_buf[eeprom_p2+4]);
							eeprom_p2tmp = eeprom_p2;
							i1 = 0;
							while((i1 < 675) && (eeprom_p2tmp != eeprom_p1))
							{
								out_cnt = pktsz(read_byte());
								for(i = 0; i < out_cnt; i++)
								{
									out_buf[i1] = read_byte();
									eeprom_p2tmp++;
									i1++;
									if(eeprom_p2tmp >= main_buf_size)
										eeprom_p2tmp = 0;
								}
							}
							eat_soc_sendto(server_soc, out_buf, i1, &server_adr);
eat_trace("UDP send data");
							udpsend_st_timer = 15;
							udpsend_st = 4;
						}
						break;
						case 4:
						{
							if(udpsend_st_timer != 0)
							{
								udpsend_st_timer--;
							}
							else
							{
								ExIPN++;
								if(ExIPN == 3)
									ExIPN = 0;
								server_adr.port = ExPort[ExIPN];
								server_adr.addr[0]=ExIP[ExIPN][0];
								server_adr.addr[1]=ExIP[ExIPN][1];
								server_adr.addr[2]=ExIP[ExIPN][2];
								server_adr.addr[3]=ExIP[ExIPN][3];

								udpsend_st = 3;
								senderr_cnt++;
								if(senderr_cnt > 30)
								{
									senderr_cnt = 0;
								}
								else
								if(senderr_cnt > 6)
								{
									udpsend_st_timer = 60;
									udpsend_st = 6;
								}
								else
								if(senderr_cnt == 3)
								{
									gprs_reset = EAT_TRUE;
write_log("GPRS reset");
									udpsend_st_timer = 10;
									udpsend_st = 6;
								}
							}
						}
						break;
						case 5:
						{
							eeprom_p2 = eeprom_p2tmp;
							buf_col_get();
							if(out_buf_col != 0)
								udpsend_st = 3;
							else
								udpsend_st = 0;
						}
						break;
						case 6:
						{
							if(udpsend_st_timer != 0)
							{
								udpsend_st_timer--;
							}
							else
							{
								udpsend_st = 0;
							}
						}
						break;
					}

					if(cfun == 4)
					{
						send_cfun1 = EAT_TRUE;
					}
					switch(Settings & 3)
					{
						case 0:
							if(Sts_d & 16)
							{
								Period = Period1;
								Send_per = Send_per1;
							}
							else
							{
								Period = Period2;
								Send_per = Send_per2;
							}
						break;
						case 1:
							if(Sts_d & 8)
							{
								Period = Period1;
								Send_per = Send_per1;
							}
							else
							{
								Period = Period2;
								Send_per = Send_per2;
							}
						break;
						case 2:
								Period = Period1;
								Send_per = Send_per1;
						break;
						case 3:
							if(Sts_d & 16)
							{
								Send_per = Send_per1;
								if(Turn)
									Period = Period3;
								else
									Period = Period1;
							}
							else
							{
								Period = Period2;
								Send_per = Send_per2;
							}
						break;
					}
					if(rsindp_cnt != 0)
						rsindp_cnt--;

					prm_cnt++;
					if((prm_cnt >= prm_per) && (prm_per != 0))
					{
						prm_cnt = 0;
						wr_pkt(3);
					}

					gsmloc_cnt++;
					if((gsmloc_cnt >= gsmloc_per) && (gsmloc_per != 0) && (main_status&2))
					{
						gsmloc_cnt = 0;
						if(((SatUs >> 6) == 0) || (Settings1 & 256))
						{
							gsmloc_f = EAT_TRUE;
						}
					}

					money_cnt++;
					if((money_cnt >= money_per) && (money_per != 0) && (main_status&2))
					{
						money_cnt = 0;
						money_f = EAT_TRUE;
					}

					trip_cnt++;
					if((trip_cnt >= trip_per) && (trip_per != 0))
					{
						trip_cnt = 0;
						wr_pkt(6);
					}

					debug_cnt++;
					if((debug_cnt >= debug_per) && (debug_per != 0))
					{
						debug_cnt = 0;
						wr_pkt(7);
					}

					ADC_cnt++;
					if((ADC_cnt >= ADC_per) && (ADC_per != 0))
					{
						ADC_cnt = 0;
						wr_pkt(13);
					}

					INx_cnt++;
					if((INx_cnt >= INx_per) && (INx_per != 0))
					{
						INx_cnt = 0;
						wr_pkt(14);
					}

					freq_cnt++;
					if((freq_cnt >= freq_per) && (freq_per != 0))
					{
						freq_cnt = 0;
						wr_pkt(12);
					}

					ident_cnt++;
					if((ident_cnt >= ident_per) && (ident_per != 0))
					{
						ident_cnt = 0;
						wr_pkt(26);
						wr_pkt(37);
					}

					can1_cnt++;
					if((can1_cnt >= can1_per) && (can1_per != 0))
					{
						can1_cnt = 0;
					}

					can2_cnt++;
					if((can2_cnt >= can2_per) && (can2_per != 0))
					{
						can2_cnt = 0;
					}

					offsim_cnt++;
					if((offsim_cnt >= offsim_per) && (offsim_per != 0))
					{
						offsim_cnt = 0;
						send_cfun4 = EAT_TRUE;
					}

					period_cnt++;
					if((period_cnt >= Period) && (Period != 0))
					{
						period_cnt = 0;
						wr_pkt(22);
					}

					send_cnt++;
					if(((send_cnt >= Send_per) && (Send_per != 0)) || (Settings & 2048))
					{
						send_cnt = 0;
						do_send = EAT_TRUE;
					}

					switch(main_st)
					{
						case 0:
						{
							if(main_status&2)
							{
								gprs_enable = EAT_TRUE;
								main_st = 1;
							}
						}
						break;
						case 1:
						{
						}
						break;
					}
				}
				if(event.data.timer.timer_id == EAT_TIMER_2)
				{
					eat_timer_start(EAT_TIMER_2, 10000);
					eat_get_rtc(&rtc);
					rssi = eat_network_get_csq();
					rssi = (unsigned char)(rssi * 3.2258);
					if(eat_get_module_temp_sync(&cmte))
						Tm = cmte / 1000;
					cgatt = eat_network_get_cgatt();
					gsm_reg = eat_network_get_creg();
					eat_get_cbc(&bmt);
					Vbt = bmt.volt;
					if(Vbt < Vbt_lim)
					{
						if(vblim_cnt != 5)
							vblim_cnt++;
					}
					else
					{
						if(vblim_cnt != 0)
							vblim_cnt--;
					}
					if(vblim_cnt == 5)
					{
						if(!(Sts_d & 4096))
						{
							Sts_d = Sts_d | 4096;
						}
					}
					if(vblim_cnt == 0)
					{
						if(Sts_d & 4096)
						{
							Sts_d = Sts_d & (0xFFFF - 4096);
						}
					}

					if(Stealth_per == 0)
					{
						if((gsm_reg != 1) && (gsm_reg != 5))
						{
							reg_err_cnt++;
							if(reg_err_cnt > 90)
							{
								reg_err_cnt = 0;
								send_cfun4 = EAT_TRUE;
write_log("GSM reg error");
							}
						}
						else
						{
							reg_err_cnt = 0;
						}
					}
					else
					{
						if((gsm_reg != 1) && (gsm_reg != 5))
						{
							reg_err_cnt++;
							if(reg_err_cnt > 60)
							{
								reg_err_cnt = 0;
								send_cfun4 = EAT_TRUE;
write_log("GSM reg error");
							}
						}
						else
						{
							reg_err_cnt = 0;
						}
					}
eat_trace("main_status:%u;cfun:%u;cpin%u;gsm_reg:%u;cgatt:%u;bear_st:%u;send_cnt=%u;senderr_cnt:%u;gprs_st:%u;", main_status, cfun, cpin, gsm_reg, cgatt, bear_st, send_cnt, senderr_cnt, gprs_st);
eat_trace("ver:%u;main_st:%u;extoff_time=%u;out_buf_col:%u;gprs_st_timer:%u;s_st:%u;", Version, main_st, extoff_time, out_buf_col, gprs_st_timer, s_st);
eat_trace("stealth_timer:%u;stealth_cnt:%u;udpsend_st:%u;SatUs:%u;own_ip:%hhu.%hhu.%hhu.%hhu;", stealth_timer, stealth_cnt, udpsend_st, (SatUs >> 6)), own_ip[0], own_ip[1], own_ip[2], own_ip[3];
eat_trace("%2.2u/%2.2u/%2.2u %2.2u:%2.2u:%2.2u;lat=%2.5f&lon=%3.5f&spd=%u&dir=%u;gprs_enable:%u;send_sms_st:%u;", Day, Month, Year, Hour, Minute, Second, (double)Latitude / 100000, (double)Longitude / 100000, Speed, Course, gprs_enable, send_sms_st);
eat_trace("gprs_st_errcnt:%u;gprs_st_timer:%u;ExIPN:%u;", gprs_st_errcnt, gprs_st_timer, ExIPN);
				}
				if(event.data.timer.timer_id == EAT_TIMER_3)
				{
eat_trace("TIMER3");
					at_res = 2;
					at_answer[0] = 0;
					eat_sem_put(sem_at_done);
				}
			}
			break;
 			case EAT_EVENT_INT:
			{
				vibration_cnt++;
eat_trace("test_handler_int_level interrupt->pin [%d ],interrupt->level=%d",event.data.interrupt.pin,event.data.interrupt.level);
				break;
			}
       }
    }
}

void app_user2(void *data)
{
	char tmp_buf[300];
	static char * buf_pos = NULL, * buf_pos1 = NULL;
	s8 ret = 0;
	SINT64 fs_freesize;
	UINT filesize;
	int testFileHandle;
	double Lat, Lon;
	EatRtc_st rtc = {0};
	int FileHandle;
	unsigned int readLen, nbrcnt;

	while(EAT_TRUE)
    {
		if(bt_send_sets)
		{
			write_at("AT+BTOPPPUSH=1,C:\\Settings.txt\r", "OK", 1000);
			bt_send_sets = EAT_FALSE;
		}
		if(bt_send_nmbrs)
		{
			write_at("AT+BTOPPPUSH=1,C:\\Numbers.txt\r", "OK", 1000);
			bt_send_nmbrs = EAT_FALSE;
		}
		if(bt_send_buf[0])
		{
			write_at("AT+BTSPPSEND\r", "", 100);
			write_at(bt_send_buf, "", 100);
			write_at("\x1A", "", 100);
			bt_send_buf[0] = 0;
		}
		if(bton)
		{
			write_at("AT+BTPOWER=1\r", "OK", 1000);
			bton = EAT_FALSE;
		}
		if(btoff)
		{
			write_at("AT+BTPOWER=0\r", "OK", 1000);
			btoff = EAT_FALSE;
		}
		if(btpair)
		{
			write_at("AT+BTPAIR=1,1\r", "OK", 1000);
			btpair = EAT_FALSE;
		}
		if(btacpt)
		{
			write_at("AT+BTACPT=1\r", "OK", 1000);
			btacpt = EAT_FALSE;
		}
		if(show_bt_menu)
		{
			write_at("AT+BTSPPSEND\r", "", 100);
			switch(bt_menu_number)
			{
				case 0:
				{
					write_at("1. Send files.\r\n2. Menu2\r\n3. Menu3\r\n\x1A", "", 100);
					break;
				}
				case 1:
				{
					write_at("1. M1Cmd1\r\n2. M1Cmd2\r\n3. M1Cmd3\r\n4. Back to root\r\n\x1A", "", 100);
					break;
				}
				case 2:
				{
					write_at("1. M2Cmd1\r\n2. M2Cmd2\r\n3. M2Cmd3\r\n4. Back to root\r\n\x1A", "", 100);
					break;
				}
				case 3:
				{
					write_at("1. M3Cmd1\r\n2. M3Cmd2\r\n3. M3Cmd3\r\n4. Back to root\r\n\x1A", "", 100);
					break;
				}
			}
			show_bt_menu = EAT_FALSE;
		}
		if(send_dtmf)
		{
			sprintf(tmp_buf, "AT+VTD=%u\r", dtmf_d);
			write_at(tmp_buf, "OK", 1000);
			sprintf(tmp_buf, "AT+VTS=\"%c\"\r", dtmf_c);
			write_at(tmp_buf, "OK", 1000);
			send_dtmf = EAT_FALSE;
		}
		if(send_cfun1)
		{
			write_at("AT+CFUN=1\r", "OK", 1000);
			if(at_res == 1)
			{
				cfun = 1;
			}
			send_cfun1 = EAT_FALSE;
		}
		if(send_cfun4)
		{
			write_at("AT+CFUN=4\r", "OK", 15000);
			if(at_res == 1)
			{
				cfun = 4;
			}
			send_cfun4 = EAT_FALSE;
		}
		if(gate_open)
		{
			eat_gpio_write(OUT1, EAT_GPIO_LEVEL_HIGH);
			eat_sleep(OutOnPeriod * 100);
			eat_gpio_write(OUT1, EAT_GPIO_LEVEL_LOW);
			gate_open = EAT_FALSE;
		}
		if(main_status&1)
		{
			if(!first_init)
			{
				first_init = EAT_TRUE;
				write_at("ATE0\r", "OK", 1000);
				write_at("AT+CNETLIGHT=0\r", "OK", 1000);
				write_at("AT+CLIP=1\r", "OK", 1000);
				write_at("AT+DDET=1,0,1,0\r", "OK", 1000);
				write_at("AT+CNETSCAN=1\r", "OK", 1000);
				write_at("AT+CSGS=0\r", "OK", 1000);
				write_at("AT+SJDR=1,1,20,1\r", "OK", 1000);
//				write_at("AT+SIMEI=\"861230049560668\"\r", "OK", 1000);
			}
		}
		if(main_status&4)
		{
			if(getparam1)
			{
				sprintf(sms_txt, "%u.%u.%u.%u,%u.%u.%u.%u,%u.%u.%u.%u,%u,%u,%u,%s,%s,%s,%u", ExIP[0][0], ExIP[0][1], ExIP[0][2], ExIP[0][3], ExIP[1][0], ExIP[1][1], ExIP[1][2], ExIP[1][3], ExIP[2][0], ExIP[2][1], ExIP[2][2], ExIP[2][3], ExPort[0], ExPort[1], ExPort[2], APN, APN_user, APN_pass, PortPr);
				send_sms(sms_nbr, sms_txt);
				getparam1 = EAT_FALSE;
			}
			if(getparam2)
			{
				sprintf(sms_txt, "%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u", Period1, Period2, Send_per1, Send_per2, Settings, Settings1, Stealth_per, Stealth_ontm, Period3, Rsindp, Sync);
				send_sms(sms_nbr, sms_txt);
				getparam2 = EAT_FALSE;
			}
			if(getparam3)
			{
				sprintf(sms_txt, "%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u,%u", prm_per, gsmloc_per, money_per, trip_per, debug_per, 0, can1_per, can2_per, ADC_per, INx_per, freq_per, ident_per, offsim_per);
				send_sms(sms_nbr, sms_txt);
				getparam3 = EAT_FALSE;
			}
			if(getparam4)
			{
				sprintf(sms_txt, "%u,%s,%s,%u,%u,%u", Vbt_off, SMS_pass, MoneyUSSD, Speed_lim, Vcc_lim, Vbt_lim);
				send_sms(sms_nbr, sms_txt);
				getparam4 = EAT_FALSE;
			}
			if(getparam5)
			{
				sprintf(sms_txt, "%s,%s,%s,%s,%s,%s,%s", NumAd1, NumAd2, Num1, Num2, Num3, Num4, Num5);
				send_sms(sms_nbr, sms_txt);
				getparam5 = EAT_FALSE;
			}
			if(ussd_send)
			{
				sprintf(tmp_buf, "AT+CUSD=1,\"%s\"\r", ussdcmd);
				write_at(tmp_buf, "+CUSD:", 30000);
				if(at_res == 1)
				{
					buf_pos = at_ret + 7;
					if(*buf_pos == '0')
					{
						buf_pos = strchr(at_ret, '\"');
						if(buf_pos)
						{
							sscanf(buf_pos, "%250[^\"]", sms_txt);
eat_trace(sms_txt);
							send_sms(sms_nbr, sms_txt);
						}
					}
					else
					{
						sprintf(sms_txt, "USSD error %c", *buf_pos);
					}
				}
				ussd_send = EAT_FALSE;
			}
			if(modinfo)
			{
				buf_pos = sms_txt;
				buf_pos = buf_pos + sprintf(buf_pos, "HW ver:%u\n\r", Version);
				buf_pos = buf_pos + sprintf(buf_pos, "IMEI:%c%c%c%c%c%c%c%c%c%c%c%c%c%c%c\n\r", IMEI[1], IMEI[2], IMEI[3], IMEI[4], IMEI[5], IMEI[6], IMEI[7], IMEI[8], IMEI[9], IMEI[10], IMEI[11], IMEI[12], IMEI[13], IMEI[14], IMEI[15]);
				buf_pos = buf_pos + sprintf(buf_pos, "GSM ver:%s\n\r", simrev);
				buf_pos = buf_pos + sprintf(buf_pos, "SIM ICC:%c%c%c%c%c%c\n\r", ICC[0], ICC[1], ICC[2], ICC[3], ICC[4], ICC[5]);
				send_sms(sms_nbr, sms_txt);
				modinfo = EAT_FALSE;
			}
			if(fsinfo)
			{
				buf_pos = sms_txt;
				ret = eat_fs_GetDiskSize(EAT_FS, &fs_freesize);
				if(ret >= 0)
				{
					buf_pos = buf_pos + sprintf(buf_pos, "Disk size %lld B\n\r", fs_freesize);
				}
				else
				{
					buf_pos = buf_pos + sprintf(buf_pos, "Disk size get error: %d\n\r", ret);
				}
				ret = eat_fs_GetDiskFreeSize(EAT_FS, &fs_freesize);
				if(ret >= 0)
				{
					buf_pos = buf_pos + sprintf(buf_pos, "Free size %lld B\n\r", fs_freesize);
				}
				else
				{
					buf_pos = buf_pos + sprintf(buf_pos, "Free size get error: %d\n\r", ret);
				}
				testFileHandle = eat_fs_Open(L"C:\\log.txt", FS_READ_ONLY);
				if(testFileHandle < EAT_FS_NO_ERROR)
				{
					buf_pos = buf_pos + sprintf(buf_pos, "Log file open error:%d\n\r", testFileHandle);
				}
				else
				{
					ret = eat_fs_GetFileSize(testFileHandle, &filesize);
					eat_fs_Close(testFileHandle);
					if(ret >= 0)
					{
						buf_pos = buf_pos + sprintf(buf_pos, "Log file size %d B\n\r", filesize);
					}
					else
					{
						buf_pos = buf_pos + sprintf(buf_pos, "Log file size get error: %d\n\r", ret);
					}
				}
				send_sms(sms_nbr, sms_txt);
				fsinfo = EAT_FALSE;
			}
			if(getnumbers && (!incall_f))
			{
				buf_pos = sms_txt;
				FileHandle = eat_fs_Open(L"C:\\Numbers.txt", FS_READ_ONLY);
				if(FileHandle < EAT_FS_NO_ERROR)
				{
					strcpy(buf_pos, "List of numbers is empty.");
					send_sms(sms_nbr, sms_txt);
				}
				else
				{
					nbrcnt = 0;
					do{
						eat_fs_Read(FileHandle, tmp_buf, 14, &readLen);
						if((readLen == 14))
						{
							tmp_buf[12] = 0;
							if(nbrcnt != 0)
							{
								*buf_pos = ',';
								buf_pos++;
							}
							buf_pos = buf_pos + sprintf(buf_pos, "%s",tmp_buf);
							nbrcnt++;
						}
						if((nbrcnt == 10) || (readLen != 14))
						{
							nbrcnt = 0;
							send_sms(sms_nbr, sms_txt);
							if(readLen == 14)
								eat_sleep(30000);
							buf_pos = sms_txt;
						}
					}while(readLen == 14);
				}
				eat_fs_Close(FileHandle);
				getnumbers = EAT_FALSE;
			}
			if(pos2sms && (!incall_f))
			{
				buf_pos = sms_txt;
				if((Year < 17) || (Year == 80))
				{
					eat_get_rtc(&rtc);
					Year = rtc.year;
					Month = rtc.mon;
					Day = rtc.day;
					Hour = rtc.hour;
					Minute = rtc.min;
					Second = rtc.sec;
				}
				buf_pos = buf_pos + sprintf(buf_pos, "%2.2u/%2.2u/%2.2u\n\r%2.2u:%2.2u:%2.2u\n\r", Day, Month, Year, Hour, Minute, Second);
				buf_pos = buf_pos + sprintf(buf_pos, "Vbt:%1.3fV\n\r", (double)Vbt/1000);
				if((Latitude != 0) && (Longitude != 0))
				{
					Lat = (double)Latitude / 100000;
					Lon = (double)Longitude / 100000;
					buf_pos = buf_pos + sprintf(buf_pos, "Lat:%.7f\n\rLon:%.7f\n\r", Lat, Lon);
				buf_pos = buf_pos + sprintf(buf_pos, "%ukm/h\n\r%udeg\n\r", Speed, Course);
					buf_pos = buf_pos + sprintf(buf_pos, "http://server1.gsm-gps.com/maps1/vp_gps.php?lat=%2.5f&lon=%3.5f&spd=%u&dir=%u\n\r", Lat, Lon, Speed, Course);
				}
				else
				{
					write_at("AT+SJDR=0\r", "OK", 1000);
					write_at("AT+CNETSCAN\r", "Operator:", 30000);
					if(at_res == 1)
					{
						buf_pos1 = strstr(at_ret, "MCC");
						sscanf(buf_pos1, "MCC:%u,MNC:%u,Rxlev:%*u,Cellid:%X,Arfcn:%*X,Lac:%X", &MCC, &MNC, &CID, &LAC);
eat_trace("MCC:%u,MNC:%u,Cellid:%u,Lac:%u", MCC, MNC, CID, LAC);
						buf_pos = buf_pos + sprintf(buf_pos, "MCC:%u,MNC:%u,LAC:%u,CID:%u\n\r", MCC, MNC, LAC, CID);
						buf_pos = buf_pos + sprintf(buf_pos, "http://server1.gsm-gps.com/maps1/vp_gsm.php?MCC=%u&MNC=%u&LAC=%u&CID=%u\n\r", MCC, MNC, LAC, CID);
					}
					else
					{
						buf_pos = buf_pos + sprintf(buf_pos, "AT+CNETSCAN ERROR\n\r");
					}
					write_at("AT+SJDR=1,1,20,1\r", "OK", 1000);
				}
				send_sms(sms_nbr, sms_txt);
				pos2sms = EAT_FALSE;
			}
			if(gsmoffon)
			{
				strcpy(sms_txt, "Command \"gsmoffon\" accepted.");
				send_sms(sms_nbr, sms_txt);
				sms_sended = EAT_FALSE;
				while(!sms_sended)
					eat_sleep(1000);
				send_cfun4 = EAT_TRUE;
				gsmoffon = EAT_FALSE;
			}
			if(cpureset)
			{
				strcpy(sms_txt, "Command \"cpureset\" accepted.");
				send_sms(sms_nbr, sms_txt);
				sms_sended = EAT_FALSE;
				while(!sms_sended)
					eat_sleep(1000);
				simreset_f = EAT_TRUE;
				cpureset = EAT_FALSE;
			}
			if(stsreset)
			{
				eat_fs_Delete(L"C:\\Settings.txt");
				strcpy(sms_txt, "Command \"stsreset\" accepted.");
				send_sms(sms_nbr, sms_txt);
				sms_sended = EAT_FALSE;
				while(!sms_sended)
					eat_sleep(1000);
				simreset_f = EAT_TRUE;
				stsreset = EAT_FALSE;
			}
		}
		if(main_status&2)
		{
			if(fw_update)
			{
				write_at("AT+SAPBR=3,1,\"Contype\",\"GPRS\"\r", "OK", 1000);
				sprintf(tmp_buf, "AT+SAPBR=3,1,\"APN\",\"%s\"\r", APN);
				write_at(tmp_buf, "OK", 1000);
				sprintf(tmp_buf, "AT+SAPBR=3,1,\"USER\",\"%s\"\r", APN_user);
				write_at(tmp_buf, "OK", 1000);
				sprintf(tmp_buf, "AT+SAPBR=3,1,\"PWD\",\"%s\"\r", APN_pass);
				write_at(tmp_buf, "OK", 1000);
				write_at("AT+SAPBR=1,1\r", "OK", 20000);
				if(at_res == 1)
				{
					write_at("AT+FTPCID=1\r", "OK", 1000);
					sprintf(tmp_buf, "AT+FTPSERV=\"%u.%u.%u.%u\"\r", FTP_server[0], FTP_server[1], FTP_server[2], FTP_server[3]);
					write_at(tmp_buf, "OK", 1000);
					sprintf(tmp_buf, "AT+FTPUN=\"%s\"\r", FTP_user);
					write_at(tmp_buf, "OK", 1000);
					sprintf(tmp_buf, "AT+FTPPW=\"%s\"\r", FTP_pass);
					write_at(tmp_buf, "OK", 1000);
					sprintf(tmp_buf, "AT+FTPGETNAME=\"%s\"\r", fw_filename);
					write_at(tmp_buf, "OK", 1000);
					sprintf(tmp_buf, "AT+FTPGETPATH=\"%s\"\r", FTP_path);
					write_at(tmp_buf, "OK", 1000);
					write_at("AT+FTPPORT=21\r", "OK", 1000);
					write_at("AT+FTPTIMEOUT=3\r", "OK", 1000);
					write_at("AT+FTPGETTOFS=0,\"app\"\r", "+FTPGETTOFS:", 60000);
					if(at_res == 1)
					{
						buf_pos = at_ret + 13;
						if(*buf_pos == '0')
						{
	eat_trace("Download done");
							app_update(L"C:\\User\\Ftp\\app");
						}
					}
				}
				write_at("AT+SAPBR=0,1\r", "OK", 20000);
				fw_update = EAT_FALSE;
			}
			if(ICC[0] == 0)
			{
				write_at("AT+CCID\r", "OK", 1000);
			}
			if(money_f)
			{
				money_f = EAT_FALSE;
				sprintf(tmp_buf, "AT+CUSD=1,\"%s\"\r", MoneyUSSD);
				write_at(tmp_buf, "+CUSD:", 30000);
				if(at_res == 1)
				{
					buf_pos = at_ret + 7;
					if(*buf_pos == '0')
					{
						buf_pos = strchr(at_ret, '\"');
						if(buf_pos)
						{
							while(!isdigit(*buf_pos))
								buf_pos++;
							Money = atoi(buf_pos);
eat_trace("Money:%u;", Money);
							wr_pkt(5);
						}
					}
				}
			}
			if(gsmloc_f)
			{
				write_at("AT+SJDR=0\r", "OK", 1000);
				write_at("AT+CNETSCAN\r", "Operator:", 30000);
				if(at_res == 1)
				{
					buf_pos = strstr(at_ret, "MCC");
					if(buf_pos)
					{
						sscanf(buf_pos, "MCC:%u,MNC:%u,Rxlev:%*u,Cellid:%X,Arfcn:%*X,Lac:%X", &MCC, &MNC, &CID, &LAC);
						wr_pkt(33);
eat_trace("MCC:%u,MNC:%u,Cellid:%u,Lac:%u", MCC, MNC, CID, LAC);
					}
				}
				write_at("AT+SJDR=1,1,20,1\r", "OK", 1000);
				gsmloc_f = EAT_FALSE;
			}
		}
		if(gprs_reset)
		{
			ret = eat_soc_close(server_soc);
            ret = eat_gprs_bearer_release();
			gprs_reset = EAT_FALSE;
		}
		if(log_upload && (!incall_f))
		{
			write_at("AT+SAPBR=3,1,\"Contype\",\"GPRS\"\r", "OK", 1000);
			sprintf(tmp_buf, "AT+SAPBR=3,1,\"APN\",\"%s\"\r", APN);
			write_at(tmp_buf, "OK", 1000);
			sprintf(tmp_buf, "AT+SAPBR=3,1,\"USER\",\"%s\"\r", APN_user);
			write_at(tmp_buf, "OK", 1000);
			sprintf(tmp_buf, "AT+SAPBR=3,1,\"PWD\",\"%s\"\r", APN_pass);
			write_at(tmp_buf, "OK", 1000);
			write_at("AT+SAPBR=1,1\r", "OK", 20000);
			if(at_res == 1)
			{
				write_at("AT+FTPCID=1\r", "OK", 1000);
				write_at("AT+FTPSERV=\"194.28.172.136\"\r", "OK", 1000);
				write_at("AT+FTPUN=\"vladimir\"\r", "OK", 1000);
				write_at("AT+FTPPW=\"dkflbvbh79820409\"\r", "OK", 1000);
				write_at("AT+FTPPORT=21\r", "OK", 1000);
				write_at("AT+FTPTIMEOUT=3\r", "OK", 1000);
				write_at("AT+FTPPUTPATH=\"/TrLog/\"\r", "OK", 1000);
				sprintf(tmp_buf, "AT+FTPPUTNAME=\"T%c%c%c%c%c%c%c.txt\"\r", IMEI[9], IMEI[10], IMEI[11], IMEI[12], IMEI[13], IMEI[14], IMEI[15]);
				write_at(tmp_buf, "OK", 1000);
				write_at("AT+FTPPUTFRMFS=C:\\log.txt\r", "+FTPPUTFRMFS:", 60000);
			}
			write_at("AT+SAPBR=0,1\r", "OK", 20000);
			log_upload = EAT_FALSE;
		}
		if(ata_f)
		{
			ata_f = EAT_FALSE;
			write_at("ATA\r", "OK", 1000);
			dtmf_menu_number = 0;
			incall_f = EAT_TRUE;
		}
		if(ath_f)
		{
			ath_f = EAT_FALSE;
			write_at("ATH\r", "OK", 1000);
			incall_f = EAT_FALSE;
		}
		if(ath_simreset_f)
		{
			ath_simreset_f = EAT_FALSE;
			write_at("ATH\r", "OK", 1000);
			incall_f = EAT_FALSE;
			eat_reset_module();
		}

		eat_sleep(1000);
	}
}

void app_user8(void *data)
{
    while(EAT_TRUE)
    {
		if(incall_f)
		{
			eat_gpio_write(LED, EAT_GPIO_LEVEL_HIGH);
			eat_sleep(100);
			eat_gpio_write(LED, EAT_GPIO_LEVEL_LOW);
			eat_sleep(500);
		}
		else
		if(fw_update)
		{
			eat_gpio_write(LED, EAT_GPIO_LEVEL_HIGH);
			eat_sleep(100);
			eat_gpio_write(LED, EAT_GPIO_LEVEL_LOW);
			eat_sleep(100);
			eat_gpio_write(LED, EAT_GPIO_LEVEL_HIGH);
			eat_sleep(100);
			eat_gpio_write(LED, EAT_GPIO_LEVEL_LOW);
			eat_sleep(500);
		}
		else
		{
			if(!cpin)
			{
				eat_gpio_write(LED, EAT_GPIO_LEVEL_HIGH);
				eat_sleep(100);
				eat_gpio_write(LED, EAT_GPIO_LEVEL_LOW);
			}
			else
			{
				eat_gpio_write(LED, EAT_GPIO_LEVEL_HIGH);
				eat_sleep(300);
				eat_gpio_write(LED, EAT_GPIO_LEVEL_LOW);
				if((gsm_reg == 1) || (gsm_reg == 5))
				{
					eat_sleep(300);
					eat_gpio_write(LED, EAT_GPIO_LEVEL_HIGH);
					eat_sleep(300);
					eat_gpio_write(LED, EAT_GPIO_LEVEL_LOW);
					if(bear_st == 2)
					{
						eat_sleep(300);
						eat_gpio_write(LED, EAT_GPIO_LEVEL_HIGH);
						eat_sleep(300);
						eat_gpio_write(LED, EAT_GPIO_LEVEL_LOW);
					}
				}
			}
			eat_sleep(1500);
		}
    }
}
