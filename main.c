#include "led.h"
#include "delay.h"
#include "sys.h"
#include "usart.h"	 
#include "pstwo.h"
#include "time.h"
#include "dma.h"
#include "motor.h"
#include <math.h>
#include <string.h>
#include "control.h"
#include "oled.h"
#include "stm32f10x_adc.h"
#include "PID_SZJ.h"

#define little 1900
#define ang_1  0
#define ang_2  180
#define ang_3  270
#define ang_4  90
#define ang_tem 2//2.5
#define ang_level  0.5
#define ang_max  4
#define AA 10
#define BB 180 
#define Ld 1.8
#define set_270 270
#define vel_0 300  //300
#define vel_1 400
#define vel_2 500//500
#define  velcity1  2300
#define  B  20
#define  B_1  20
#define  normal  170
#define  work_pwm  975
#define  nowork_pwm  1900

//当前小车轮子的直径为67mm其周长为21cm；需要18.5圈跑完390cm的长度，一圈的脉冲数为390 则390*18.5 为预期的脉冲数
//设在390*16.5个脉冲后车子减速，*17.5个时车子停止，并开始转弯
//设场地宽度的实际行驶距离为300cm-30cm=270cm  270/21=12.8,则11.8时减速，12.8时停止并转弯    陇间的中心距离为70cm 合计3.33圈，但行驶过程中需要保持在中间位置
int pulse1, pulse2,pulse3,pulse4;//设记录脉冲数的变量为pulse1 2 3 4 
int guang_1 = 0;
extern u8 u3_RxBuffer[USART3_RXBUF_SIZE];//导航数据缓存空间 DMA接收地址
extern u8 u4_RxBuffer[UART4_RXBUF_SIZE];//导航数据缓存空间 DMA接收地址
int R,Y;
int fg_1=0;
float set_angle=0;
int tree_num[10]={0,0,0,0,0,0,0,0,0,0};//用于记录果树施肥数量，0为5，1为10表示舵机转两次
u8 flag_finsh=0;//表示本次施肥完毕。只有施肥完毕之后才能开始下一次预装载
u8 flag_over = 0;//表示本次预装载完毕
u8 start = 0,stop_2=0;
u8 buf[5]={'1','2','3','s','e'};//1 识别颜色  2 识别二维码 3停止识别颜色 's'表示动作舵机
float h=89.5,j=90.5;
float h_1=89.5,j_1=90.5;
float X=15,X_1=14;
int flag_Dir=1;
extern int jg3_1,jg4_1,jg2_1;
extern float Line_buf1[5];
extern uint16_t  ADCBuf[3];					// ADC数据缓存
int base_0 =265;
float kp_0=1.18,kd_0=0.10,ki_0=0.33;//50//转弯
float r=15.5;
extern u8 jg0,jg1,jg2,jg3,jg4,jg5;//各个光电的标志位jg0为正前方的传感器；jg1为左前方的传感器
//jg1为左前方的传感器,第一条直线时，依靠左前方
extern float Rotate1,Rotate2,Rotate3,Rotate4;
extern float	angle,ultra_0,ultra_1;
unsigned char  uart3buf[40];//  导航处理数据缓存空间
unsigned char  uart4buf[10];//  导航处理数据缓存空间
u8 run_level = 0;
u8 page = 2;//初始为零、后续增加页面显示 为零时显示转速信息
u8 enable = 1;//使能键
u8 yellow = 0,red = 0,row = 0,mode = 1;
int indicate = 6;
u8 dt_0=2,dt_1=5;
u8 tt=1;
int R_0=0,L_0=0;
int Yaw_pwm,Vel_pwm,New_pwm;
int a ,b ,c ,d ;
int N = 0;//用于计数第几个弯
float Res;
int flag_right_mv=0;
u8 flag=1,flag_k=0;
u8 ad_1=1;
	u8 cz;
int flag_turn_start=0,flag_turn_end=1,fast_segment,media_segment,low_segment;
u8 ad=1;
u8 judge_flag= 0;
STATUS_SEG flag_Status;

////直行程序7-23//////

int yuzhi(int x){

if(x>3190)
	x=3190;
return x;
}


int No=1;
int myabs(int a)
{ 		   
	  unsigned int temp;
		if(a<0)  temp=abs(a);  
	  else temp=a;
	  return temp;
}


void SetPWM_Position_ZF(int pwm[])//2022 7 25 正反转的PWM控制
{
  if(pwm[0]>=0)//pwm>=0 (BIN1, BIN2)=(0, 1) 正转
  {
		left1_z();
		TIM1->CCR1=pwm[0];
  }else{
		left1_f();
		TIM1->CCR1=-pwm[0];
	}
	 if(pwm[1]>=0)//pwm>=0 (BIN1, BIN2)=(0, 1) 正转
  {
		left2_z();
		TIM1->CCR2=pwm[1];
  }else{
		left2_f();
		TIM1->CCR2=-pwm[1];
	}
	if(pwm[2]>=0)//pwm>=0 (BIN1, BIN2)=(0, 1) 正转
  {
		right2_z();
		TIM1->CCR3=pwm[2];
  }else{
		right2_f();
		TIM1->CCR3=-pwm[2];
	}
	if(pwm[3]>=0)//pwm>=0 (BIN1, BIN2)=(0, 1) 正转
  {
		right1_z();
		TIM1->CCR4=pwm[3];
  }else{
		right1_f();
		TIM1->CCR4=-pwm[3];
	}

}




//float angle_to_rad(float i){
//    float ang_t;

//    return ang_t = i/180*pi;
//}
u8 yu=1;

////直行程序7-23//////
u8 cz = 1;
int l=0,m=0,y=0,z=0,mv=0;
float Y_1=6.5,Y_2=7.5,Y_3=20;
float Y_4=12.5,Y_5=14.8;

void Yaw_angle()                       //磁敏角度传感器前轮角度惯性元件采集 float型变量 
{		
	  unsigned char  Receive_len,Byte_high,Byte_low;
	float res;   //Byte_high_inv,Byte_low_inv;               	                      

    /////////采数据程序///////
	  USART3_Receive_Data(uart3buf,&Receive_len);         //*p=&i,指针变量在定义中允许带初始化项
    if(Receive_len)
		{
			if((uart3buf[0]==0x55)&&(uart3buf[1]==0x51))       //起始位和结束位数据校验
			{
//滚转角（x 轴）Roll=((RollH<<8)|RollL)/32768*180(°) 
//俯仰角（y 轴）Pitch=((PitchH<<8)|PitchL)/32768*180(°) 
//偏航角（z 轴）Y aw=((Y awH<<8)|YawL)/32768*180(°) 
				//OLED_ShowChar(78,5,uart3buf[22],15);
				Byte_low = uart3buf[28];
				Byte_high = uart3buf[29];
				res = (short)(Byte_high<<8| Byte_low);
				angle = res/32768.0*180;
				if(angle<0){
				angle = angle+360;
				}
			}
		}

}
int extra_work,stop_1=0,cstart=1,working=0;//,number_fei;
u8 num_r=0,num_y=0,num_p=0,flag_r=0,guang_2=1;
int set_du(int du){
	int i;

		i=500+du*5.55;
	return i;
}

void go_into_end(){
		//delay_ms(50);
				if(flag_Dir){
					go();
					}else{
					back();
					}
}
int led_flag=0,flag_extra=0;


typedef struct num_MOTOR{

	int left_door;
	int left_1;
	int left_2;
	int left_hit;
	
	int right_door;
	int right_1;
	int right_2;
	int right_hit;

}steering_gear;

steering_gear gear_open = {1250,1900,1850,1500+700,2500-750,1100,1100,1500-700};
steering_gear gear_close = {500,500,500,1500,2500,2500,2500,1500};
/**************************
N_row表示行 0~12
color表示识别到的颜色 
direction 表示方向 左0‘ ’右1
*************************/
void Control_Notify(uint8 N_row,uint8 direction)
{
	if(N_row%2==1)//在奇数行，则需要作业
	{
		if(N_row == 1||N_row == 11)
		{
			ServoPwmDuty[0]=gear_close.left_door;//左侧关闭
			ServoPwmDuty[4]=gear_open.right_door;//右侧打开
		}else
		{
			ServoPwmDuty[0]=gear_open.left_door;//左侧打开
			ServoPwmDuty[4]=gear_open.right_door;//右侧打开
		}

	}//if _ end
	if(flag_turn_start){
		
		 ServoPwmDuty[0]=gear_close.left_door;//左侧关闭
		 ServoPwmDuty[4]=gear_close.right_door;//右侧关闭
		 ServoPwmDuty[3] = gear_close.left_hit;////击打装置 关闭
		 ServoPwmDuty[7] = gear_close.right_hit;////击打装置 关闭
		
	}
}

void OpenMv_left()                       //磁敏角度传感器前轮角度惯性元件采集 float型变量 
{		
	  unsigned char  Receive_len;
	//float res;   //Byte_high_inv,Byte_low_inv;               	                      
	
    /////////采数据程序///////
	  UART4_Receive_Data(uart4buf,&Receive_len);         //*p=&i,指针变量在定义中允许带初始化项
    if(Receive_len)
		{			
			if(uart4buf[0]==0x53){//head-start
				
				switch(uart4buf[1])
				{
					case 0x30://绿色
										ServoPwmDuty[3] = gear_close.left_hit;
										break;
					case 0x31://黄色
										ServoPwmDuty[1] = gear_close.left_1;
										ServoPwmDuty[2] = gear_close.left_2;					
										ServoPwmDuty[3] = gear_open.left_hit;
										break;
					case 0x32://红色
										ServoPwmDuty[1] = gear_close.left_1;
										ServoPwmDuty[2] = gear_open.left_2;
										ServoPwmDuty[3] = gear_open.left_hit;
										break;
					case 0x33://黑色
										ServoPwmDuty[1] = gear_open.left_1;
										ServoPwmDuty[2] = gear_open.left_2;	
										ServoPwmDuty[3] = gear_open.left_hit;
										break;
				}
			}//head-end
		}//_len

}
void OpenMv_right()                       //磁敏角度传感器前轮角度惯性元件采集 float型变量 
{		
		u8 right_mv[5];
    if(flag_right_mv)
		{		
			flag_right_mv=0;
			memcpy(right_mv,Remote_data5,5);
			if(right_mv[0]==0x53){//head-start
				
				switch(right_mv[1])
				{
					case 0x30://绿色
										ServoPwmDuty[7] = gear_close.right_hit;
										break;
					case 0x31://黄色
										ServoPwmDuty[5] = gear_close.right_1;
										ServoPwmDuty[6] = gear_close.right_2;					
										ServoPwmDuty[7] = gear_open.right_hit;
										break;
					case 0x32://红色
										ServoPwmDuty[5] = gear_close.right_1;
										ServoPwmDuty[6] = gear_open.right_2;
										ServoPwmDuty[7] = gear_open.right_hit;
										break;
					case 0x33://黑色
										ServoPwmDuty[5] = gear_open.right_1;
										ServoPwmDuty[6] = gear_open.right_2;	
										ServoPwmDuty[7] = gear_open.right_hit;
										break;
				}
			}//head-end
		}//_len

}
int count_5 = 0;
//flag_r
//static int num_t=0;//待施肥树木的编号，每次施完肥之后加1

//需要有两个模式 一个不作业 ，一个作业 两套模式能够同时运行，并可人为选择。
void color_1(){

	if((N==1||N%2==1)&&N!=11&&N!=13){//陇间 此时需要开始识别颜色
		
		if(cstart){
		
				USART_SendData(UART4,buf[0]);//识别颜色
				//while()
				cstart=!cstart;
				stop_2=1;
		}
	}else {
		if(stop_2){
		 USART_SendData(UART4,buf[2]);//停止识别颜色
			stop_2=!stop_2;
			cstart=!cstart;
		}
	}

}
u8 ss=0;
float PO;
u8 gg_1=20,gg_2=20;
int flag_start=1;
int bb_1=300,bb_0=1200;
u8 nn=1,hf=1;
//定时器3中断服务程序
u8 ultra_flag_11=1,ultra_flag_13=0;
int lun=1,ji=0,main_=1,TimeCount;
int spd_last,spd_diff;
int flag_distance_50=0;
//int PWM,PWM_P,PWM_V;
#if !Encoder
void TIM3_IRQHandler(void)   //TIM3中断
{

  if(TIM_GetITStatus(TIM3,TIM_IT_Update) !=RESET){
		mv++;
		y++;
		if(stop_1)
		{//等于1时表示识别到颜色的树苗，应当停止并进行施肥操作
			l=0;
			m=0;
			z=0;
		}else{
			l++;
			m++;
			z++;
		}
		
		if(y > 0 )
		{
			Yaw_angle();
			y=0;
			if(flag_turn_start)//开始转弯
			{
				TargetVelocity=120;
				judge_1(&N,angle);
			}
		}
		
		if(z>1)
		{
			goo();
			z=0;
		}
		
		if(l > 0)
		{
					l=0;
					if(!flag_distance_50){
							if(flag_Status == FAST_){
								TimeCount++;
								if(TimeCount<50)
									TargetVelocity=Vel_SZJ.velcity_low;
								if(TimeCount>50&&TimeCount<100){
									TargetVelocity=Vel_SZJ.velcity_media;
								}
								if(TimeCount>100)
									TargetVelocity=Vel_SZJ.velcity_max;
							}else if(flag_Status == MEDIA_)
							{
								TimeCount++;
								if(TimeCount<50)
									TargetVelocity=Vel_SZJ.velcity_low;
								if(TimeCount>100&&TimeCount<150){
									TargetVelocity=Vel_SZJ.velcity_media;
								}
							
							}else if(flag_Status == LOW_)
							{
									TargetVelocity=Vel_SZJ.velcity_low;
							}
						}
					
					gogogo_test();
		}
	TIM_ClearITPendingBit(TIM3,TIM_IT_Update);
  }
}
#else
//1 3 5 7 9 11   N
//1 2 3 4 5 6    dt_0/dt_1

int ui=0;
u8 num_set = 0;//用户设定的第num_set树苗 最大9
float juli1,juli2,juli3;
float buffer_ultra0[5],buffer_ultra1[5],buffer_ultra2[5];
char *n1 = "t:";
char *n2 = "num:";
char *n3 = "OK";
int Line_count1=0,TimeCount1=0;
int flag_clear = 0,flag_clear_2=0;
#define Count_p1 (11.28*390*0.810)  //0.80-high  0.85测试220
void TIM6_IRQHandler(void)   //TIM3中断
{
  if(TIM_GetITStatus(TIM6,TIM_IT_Update) !=RESET){

		mv++;
		y++;
		if(stop_1)
		{//等于1时表示识别到颜色的树苗，应当停止并进行施肥操作
			l=0;
			m=0;
			z=0;
		}else{
			l++;
			m++;
			z++;
		}
		
		if(y > 0 )
		{
			Yaw_angle();
			y=0;
			if(flag_turn_start)//开始转弯
			{
				TimeCount1++;
//				if(TimeCount1<50) //60 2022 9-17
//					TargetVelocity=Vel_SZJ.velcity_media;
//				else
//					TargetVelocity=Vel_SZJ.velcity_low-50;
				TargetVelocity=200;//120 2022-9-3 150 9-17
				judge_1(&N,angle);
			}
		}
		
		if(z>1)
		{
			goo();
			z=0;
			//Control_Notify(N,1);
		}
		
		if(l > 0)
		{
					l=0;
					if(!flag_distance_50){
							if(flag_Status == FAST_){
								TimeCount++;
								#if SIZE_WHEEL == 65
								if(TimeCount<30)
								{
									TargetVelocity= Vel_SZJ.velcity_low;
								}else
								if(TimeCount>30&&TimeCount<70)
									TargetVelocity=Vel_SZJ.velcity_media;
								else if(TimeCount>70&&TimeCount<100){
									TargetVelocity=Vel_SZJ.velcity_max;
								}
									
							}else if(flag_Status == MEDIA_)
							{
								TimeCount++;
								if(TimeCount<60)
									TargetVelocity=Vel_SZJ.velcity_low;
								else if(TimeCount>60&&TimeCount<80){
									TargetVelocity=Vel_SZJ.velcity_media;
								}
								else if(TimeCount>80)
									TargetVelocity=Vel_SZJ.velcity_high; //velcity_high
							
							}else if(flag_Status == LOW_)
							{
								TimeCount++;
								if(TimeCount<50)
									TargetVelocity=Vel_SZJ.velcity_low;
								else
									TargetVelocity=180;
								
								//TargetVelocity=Vel_SZJ.velcity_low; //2022-9-3
							}
								#elif SIZE_WHEEL ==76
								if(TimeCount<30)
								{
									TargetVelocity= Vel_SZJ.velcity_low;
								}else
								if(TimeCount>40&&TimeCount<70)
									TargetVelocity=Vel_SZJ.velcity_low+25;
								else if(TimeCount>70&&TimeCount<100){
									TargetVelocity=Vel_SZJ.velcity_media;
								}
								else if(TimeCount>100)
									TargetVelocity=Vel_SZJ.velcity_max;
							}else if(flag_Status == MEDIA_)
							{
								TimeCount++;
								if(TimeCount<30)
								{
									TargetVelocity= Vel_SZJ.velcity_low;
								}else
								if(TimeCount>40&&TimeCount<70)
									TargetVelocity=Vel_SZJ.velcity_low+25;
								else if(TimeCount>70&&TimeCount<100){
									TargetVelocity=Vel_SZJ.velcity_media;
								}
								else if(TimeCount>100&&TimeCount<200)
								{	TargetVelocity=Vel_SZJ.velcity_high-20; //velcity_high 
									flag_clear_2 = 1;
								}
								else if(pulse1>Count_p1)
								{TargetVelocity=60;
									if(flag_clear_2)
									{
										flag_clear_2=0;
										flag_clear = 1;
									}
									
								}
								
//								if(TimeCount<60)
//									TargetVelocity=Vel_SZJ.velcity_low;
//								else if(TimeCount>60&&TimeCount<100){
//									TargetVelocity=Vel_SZJ.velcity_media;
//								}
//								else if(TimeCount>100&&TimeCount<200)
//									TargetVelocity=Vel_SZJ.velcity_high; //velcity_high
//								else if(pulse1>Vel_SZJ.circle_media*390*0.78)
//									TargetVelocity=70;
							
							}else if(flag_Status == LOW_)
							{
								TimeCount++;
								if(TimeCount<30) //60 2022 9-17
									TargetVelocity=Vel_SZJ.velcity_low;
								else
									TargetVelocity=Vel_SZJ.velcity_low+40;
								
								//TargetVelocity=Vel_SZJ.velcity_low; //2022-9-3
							}
							#endif
						}//distance50 end
					
					gogogo_test();
		}
		if(mv>9)//100ms
		{
				mv=0;
				Rotate1 = Read_Velocity(2,&pulse1)*10*60/4.0/390.0;
				Rotate2 = Read_Velocity(3,&pulse2)*10*60/4.0/390.0;
				Rotate3 = Read_Velocity(5,&pulse3)*10*60/4.0/390.0;
				Rotate4 = Read_Velocity(4,&pulse4)*10*60/4.0/390.0;
		}

		
	TIM_ClearITPendingBit(TIM6,TIM_IT_Update);
  }
}
#endif


#define M_8 3
float lvbo_1(float Line_buf1[],int M){
	float Line_temp;
	float *Line_buf = Line_buf1;
//	memcpy(Line_buf,Line_buf1,sizeof(Line_buf1));
	//static float end_ultra;
	u8 Line_j,Line_i;
	for(Line_j=0;Line_j<M-1;Line_j++)
					{
						for(Line_i=Line_j+1;Line_i<M-Line_j;Line_i++)         
							{
								if(Line_buf[Line_i]>Line_buf[Line_i+1])
								{
									Line_temp=Line_buf[Line_i];
									Line_buf[Line_i]=Line_buf[Line_i+1];
									Line_buf[Line_i+1]=Line_temp;
								}
							}
					}
			return Line_buf[(M-1)/2];		
}
#define PWM 0
#define SORT 0
int light=0;
 int main(void)
 {
	u8 key_num;
	delay_init();	    	 //延时函数初始化	  
	NVIC_Configuration(); 	 //设置NVIC中断分组2:2位抢占优先级，2位响应优先级
	uart_IMU_init(115200);
	DMA_Receive_init(DMA1_Channel3,(u32)&USART3->DR,(u32)u3_RxBuffer,USART3_RXBUF_SIZE);//初始化串口三的DMA接收 ---用于接收导航信息
	uart_OpenMv_init(115200);//左侧
	DMA2_Receive_init(DMA2_Channel3,(u32)&UART4->DR,(u32)u4_RxBuffer,UART4_RXBUF_SIZE);//初始化串口三的DMA接收 ---用于接收导航信息
	uart_5(115200);//openmv右侧
  TIM1_Init();	 //M1  M2  M3 M4
	KEY_Init();
	GPIO_Init_01(); 
	#if PWM
		TIM5_Int_Init(200-1,7200-1);
		TIM3_Int_Init(100-1,7200-1);//改动1
		TIM7_Int_Init(3500-1,7200-1);
		TIM8_Int_Init_(20000-1,72-1);//20ms - CNT1->0.01ms   0.5ms对应0度、2.5ms对应最大180/360
		TIM_SetCompare2(TIM8,set_du(AA));	//在中间的位置开始
	 	TIM_SetCompare1(TIM8,1000);	//小舵机控制
		TIM_SetCompare3(TIM8,1000);	//小舵机控制
	 	JIG_Init();
		go();
		TIM4_Capture_Init();
		TIM_SetCompare4(TIM8,1900);//1000
		TIM2_Capture_Init();
		TIM_Cmd(TIM3, ENABLE);  //使能TIMx 	 
	#else
		TIM6_Int_Init(100-1,7200-1);
		TIM2_Int_Init(100,7200);
		TIM3_Int_Init(100,7200);
		TIM4_Int_Init(100,7200);
		TIM5_Int_Init(100,7200);
		delay_ms(100);
	#endif
	delay_ms(100);
	OLED_Init();
	PID_Init();
	ADC1_Init();
	TIM_CtrlPWMOutputs(TIM1, ENABLE);
	//InitPWM(); //此为舵机控制程序 ，暂时注释 看对于跑陇的影响
	delay_ms(50);
	stop_1=1;
	MOTO1(0, 0);
	MOTO2(0, 0);//res 小于2300之后4个轮子才会同时转
	while(1)
	{
#if !SORT		
		if(Line_count1<M_8){
			buffer_ultra0[Line_count1]=3096*(ADCBuf[0]*3.3/4096.0)/50.0;
			buffer_ultra1[Line_count1]=3096*(ADCBuf[1]*3.3/4096.0)/50.0;
			buffer_ultra2[Line_count1]=3096*(ADCBuf[2]*3.3/4096.0)/50.0;
			Line_count1++;
		}else{
				juli1=lvbo_1(buffer_ultra0,M_8);
				juli2=lvbo_1(buffer_ultra1,M_8);
				juli3=lvbo_1(buffer_ultra2,M_8);
				Line_count1=0;
		}
#else
		for(Line_count1=0;Line_count1<M_8;Line_count1++)
		{
			buffer_ultra0[Line_count1]=3096*(ADCBuf[0]*3.3/4096.0)/50.0;
			buffer_ultra1[Line_count1]=3096*(ADCBuf[1]*3.3/4096.0)/50.0;
			buffer_ultra2[Line_count1]=3096*(ADCBuf[2]*3.3/4096.0)/50.0;
			if(Line_count1>=M_8-1)
			{
				juli1=lvbo_1(buffer_ultra0,M_8);
				juli2=lvbo_1(buffer_ultra1,M_8);
				juli3=lvbo_1(buffer_ultra2,M_8);
			}
		}
#endif
		if(flag_clear)
		{
			flag_clear=0;
			clear_yaw();
		}
		if(juli3<40&&flag_turn_end&&!stop_1){
			flag_distance_50=1;
			TargetVelocity=50; //速度设置为100，减速
//			if(N==10){
//			if(juli3<12&&flag_turn_end)//当检测到距离小于20 并且转弯结束了 12.5
//			{
//						slowdown();
//						flag_zitai=0;//姿态调整标志位
//						flag_turn_end=0;//转弯结束清零
//						TargetVelocity=0;//速度清零
//						//TargetCircle=0;//距离清零
//						flag_turn_start = 1;//将 开始转弯标志位 置1
//						pulse1=0;
//						pulse2=0;
//						pulse3=0;
//						pulse4=0;
//						TimeCount=0;
//						//clean();
//			}
//		}else{
		if(juli3<11&&flag_turn_end)//当检测到距离小于20 并且转弯结束了 12.5
			{
						slowdown();
						flag_zitai=0;//姿态调整标志位
						flag_turn_end=0;//转弯结束清零
						TargetVelocity=0;//速度清零
						//TargetCircle=0;//距离清零
						flag_turn_start = 1;//将 开始转弯标志位 置1
						pulse1=0;
						pulse2=0;
						pulse3=0;
						pulse4=0;
						TimeCount=0;
						//clean();
			}
		
		}
		//}
	if(F0==0)
	{
	light = 1;
	}else if(F1==0)
	{
	light = 2;
	}else{
	light = 3;
	}
		if(page == 0&& enable==1){
				OLED_Clear();
				enable = 0;
			}else if(page == 1&& enable==1){
					OLED_Clear();
					enable = 0;
				}else if(page == 2&& enable==1){//作业模式，1为不作业，跑陇；2为作业，此时需要设置红或者黄，和第几行，设置不要作业的参数。
					OLED_Clear();
					OLED_ShowString(15,0,(unsigned char*)n1,15);
			OLED_Showdecimal(0,2,Rotate1,7,15);
			OLED_Showdecimal(0,3,Rotate2,7,15);
			OLED_Showdecimal(0,4,Rotate3,7,15);
			OLED_Showdecimal(0,5,Rotate4,7,15);//实际的右前轮
					OLED_ShowString(15,1,(unsigned char*)n2,15);        // 1
					OLED_ShowString(25,6,(unsigned char*)n3,15);//第几行
					
					enable = 0;
				}
			
			key_num = KEY_Scan(0);
			if(key_num==KEY0_PRES){
						enable = 1;
						indicate--;
						if(indicate<0)
							indicate=6;	
						ServoPwmDuty[0] = 500;
						ServoPwmDuty[1] = 500;
						ServoPwmDuty[2] = 500;
//						ServoPwmDuty[3] = 500;
						ServoPwmDuty[4] = 2500;
						ServoPwmDuty[5] = 2500;
						ServoPwmDuty[6] = 2500;
						//ServoPwmDuty[7] = 2500;
			}else if(key_num==KEY1_PRES){	
					 if(page == 1){
							run_level++;
							if(run_level >3)
							  run_level=0;
					}else if(page==2){
					switch(indicate){
						case 0:tree_num[num_set]+=1;break;
						case 1:num_set+=1;break;
						case 2:ui++;mode++;break;//TIM_SetCompare2(TIM8,set_du(AA+ui*20));break;
						case 3:R++;Y=0;break;
						case 4:Y++;R=0;break;
						case 5:row++;break;
						case 6:stop_1=0;
						pulse1=0;
						pulse2=0;
						pulse3=0;
						pulse4=0;
						flag_Status=FAST_;
						TimeCount=0;
						flag_zitai=1;
						fast_segment=1;
						break;//使能TIMx break
					}
					if(mode>1)//模式
						mode=0;
					if(tree_num[num_set]>1){
						tree_num[num_set]=0;
					}
					if(num_set>9)
						num_set=0;
					if(R == 2)//颜色
						R=0;
					if(Y==2)
						Y=0;
					if(row==6){
						row=0;
						extra_work=0;	
					}else{//行数
						if(row==1){
						extra_work=9;
						}else if(row==2){
						extra_work=7;
						}else if(row==3){
						extra_work=5;
						}else if(row==4){
						extra_work=3;
						}else if(row==5){
						extra_work=1;
						}
					}
					if(dt_0>6)//地毯
						dt_0=1;
					if(dt_1>6)
						dt_1=1;
					}
				}else if(key_num==KEY2_PRES){
						//enable = 1;
					if(page==2){
						enable = 1;
						indicate++;
						if(indicate>6)
							indicate=0;
						ServoPwmDuty[0] = 1250;
//						ServoPwmDuty[1] = 1900;
//						ServoPwmDuty[2] = 1850;
//						ServoPwmDuty[3] = 2500;
							ServoPwmDuty[4] = 2500-750; 
//						ServoPwmDuty[5] = 1100;
//						ServoPwmDuty[6] = 1100;
//						ServoPwmDuty[7] = 1500;					
//						ServoPwmDuty[1] = 500;
//						ServoPwmDuty[2] = 1850;
//						ServoPwmDuty[5] = 2500;
//						ServoPwmDuty[6] = 1100;
					}
				}
			if(page == 0){//调试界面
			OLED_Showdecimal(50,-1,Rotate1,7,15);
			OLED_Showdecimal(50,0,Rotate2,7,15);
			OLED_Showdecimal(50,1,Rotate3,7,15);
			OLED_Showdecimal(50,2,Rotate4,7,15);//实际的右前轮
			OLED_Showdecimal(50,4,angle,7,15);//角度
			OLED_Showdecimal(3,3,TIM1->CCR1,7,15);
			OLED_Showdecimal(35,3,TIM1->CCR2,7,15);
			OLED_Showdecimal(66,3,TIM1->CCR3,7,15);
			OLED_Showdecimal(98,3,TIM1->CCR4,7,15);
			OLED_Showdecimal(78,5,N,1,15);
			}else if(page == 1){//设定速度界面
			OLED_ShowNum(78,0,run_level,1,15);
			OLED_Showdecimal(50,2,Rotate1,7,15);
			OLED_Showdecimal(50,3,Rotate2,7,15);
			OLED_Showdecimal(50,4,Rotate3,7,15);
			OLED_Showdecimal(50,5,Rotate4,7,15);//实际的右前轮
			}else if(page == 2){//设置作业模式界面
				OLED_ShowChar(3,indicate,0x3e,15);//>符号用于指示选择默认为0
				OLED_Showdecimal(80,1,angle,7,15);//角度
				//OLED_ShowNum(45,6,ADCBuf[0],4,15);
				OLED_Showdecimal(80,4,juli1,7,15);
				OLED_Showdecimal(80,5,juli2,7,15);
				OLED_Showdecimal(80,6,juli3,7,15);
				
				OLED_ShowNum(80,2,TargetVelocity,4,15);
				OLED_ShowNum(80,3,TargetCircle,4,15);//TIM5CH1_CAPTURE_VAL
				OLED_ShowNum(110,-1,N,2,15);
			OLED_Showdecimal(0,2,Rotate1,7,15);
			OLED_Showdecimal(0,3,Rotate2,7,15);
			OLED_Showdecimal(0,4,Rotate3,7,15);
			OLED_Showdecimal(0,5,Rotate4,7,15);//实际的右前轮
		
			OLED_ShowNum(3, -1,TIM1->CCR1,4,12);
			OLED_ShowNum(30,-1,TIM1->CCR2,4,12);
			OLED_ShowNum(57,-1,TIM1->CCR3,4,12);
			OLED_ShowNum(84,-1,TIM1->CCR4,4,12);
#if !PWM					
			OLED_ShowNum(3,0,pulse1,5,12);
			OLED_ShowNum(3+32,0,pulse2,5,12);
			OLED_ShowNum(3+64,0,pulse3,5,12);
			OLED_ShowNum(3+96,0,pulse4,5,12);
#else
			OLED_ShowNum(3,0,TIM2->CNT,5,12);
			OLED_ShowNum(3+32,0,TIM3->CNT,5,12);
			OLED_ShowNum(3+64,0,TIM4->CNT,5,12);
			OLED_ShowNum(3+96,0,TIM5->CNT,5,12);

#endif
				OLED_ShowNum(60,2,set_angle,3,15);
				OLED_ShowNum(50,6,light,2,15);
			}
		//ServoPwmDutyCompare();
	}//while end

 
}

