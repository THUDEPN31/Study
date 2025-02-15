#set text(
  font: ("Libertinus Serif", "Source Han Serif SC"),
  lang: "zh",
  region: "cn",
)
#let title = [复变函数与数理方程期末小抄]
#let thisauthor = "钱昊远,颜浩轩"
#set document(title: [#title], author: thisauthor)
#set heading(numbering: "1.")
#set page("a4", numbering: "1", margin: (x: 1cm, y: 1cm), flipped: true)
#import "@preview/physica:0.9.3": *
#import "@preview/ctheorems:1.1.2": *
#show: thmrules

#let pst = thmbox(
  "thm",
  "公设",
  namefmt: x => [(#(strong(x)))],
  titlefmt: emph,
  inset: (x: 0em, top: 0em),
)
#let def = thmbox(
  "thm",
  "定义",
  namefmt: x => [(#(strong(x)))],
  titlefmt: emph,
  inset: (x: 0em, top: 0em),
  padding: (top: 0.1em, bottom: 0.1em),
)
#let thm = thmbox(
  "thm",
  "定理",
  namefmt: x => [(#(strong(x)))],
  titlefmt: emph,
  inset: (x: 0em, top: 0em),
)
#let coll = thmbox(
  "coll",
  "推论",
  namefmt: x => [(#(strong(x)))],
  titlefmt: emph,
  inset: (x: 0em, top: 0em),
  base: "thm",
)
#let meth = thmbox(
  "thm",
  "方法",
  namefmt: x => [(#(strong(x)))],
  titlefmt: emph,
  inset: (x: 0em, top: 0em),
)
#let case = thmbox(
  "case",
  "情形",
  namefmt: x => [(#(strong(x)))],
  titlefmt: emph,
  inset: (x: 0em, top: 0em),
)
#let exmp = thmbox("exmp", "例", titlefmt: emph, inset: (x: 0em, top: 0em))
#let sol = thmplain("sol", "解答", titlefmt: emph, inset: (x: 0em, top: 0em), base: "thm").with(numbering: none)
#let proof = thmproof("proof", "证明", inset: (x: 0em, top: 0em), titlefmt: emph, base: "thm")

#set par(leading: 1em)
#set block(spacing: 0.4em)

//可调整分列数
#show: rest => columns(3, rest, gutter: 1%)

//可调整字号
#set text(8pt)

= 常见的泰勒展开
$1/(1-z) = sum_(n = 0)^infinity z^n = 1 + z + z^2 + dots.c + z^n + dots.c $~~~~~~~~$(|z|<1)$

$e^z=sum_(n=0)^infinity 1/n! z^n = 1 + z/1! + z^2/2! + dots.c + z^n/n! + dots.c$

$sin z = sum_(n = 0)^infinity (-1)^n frac(z^(2 n + 1),(2 n + 1)!) = z - frac(z^3, 3!) + frac(z^5, 5!) + dots.c + (-1)^n frac(z^(2 n + 1),(2 n + 1)!) + dots.c$

$cos z = sum_(n = 0)^infinity (-1)^n frac(z^(2 n),(2 n)!) = 1 - frac(z^2, 2!) + frac(z^4, 4!) + dots.c + (-1)^n frac(z^(2 n),(2 n)!) + dots.c$

$(1 + z)^alpha = 1 + sum_(n = 1)^infinity frac(product_(k = 0)^(n - 1)(alpha - k), n!) z^n = 1 + alpha z + frac(alpha(alpha - 1), 2!) z^2 + dots.c + frac(alpha(alpha - 1) dots.c(alpha - n + 1), n!) z^n + dots.c$

= 孤立奇点与留数
#thm(
  "有限孤立奇点的分类"
)[\ 
  当函数$f(z)$在$0<|z-z_0|<delta(0<delta lt.eq+infinity)$内解析时：\ 
  $ lim_(z->z_0)f(z)=C_0!=infinity<==>z_0是\f(z)\的\可\去\奇\点 $
  $ lim_(z->z_0)f(z)=infinity<==>z_0是\f(z)\的\极\点 $
  $ lim_(z->z_0)(z-z_0)^m f(z)=C_(-m)!=0(m in NN_+)<==>z_0\是f(z)\的m\阶\极\点 $
  $ lim_(z->z_0)f(z)\不\存\在<==>z_0\是f(z)\的\本\性\奇\点 $]

#thm(
  "有限极点与零点的关系"
)[\ 
  若$f(z)$在$z_0$解析，那么$z_0$为$f(z)$的$m$阶零点的充要条件为\
  $f^((n))(z_0)=0$~~~~$(n=0,1,...,m-1),$~~~~$f^((m))(z_0)!=0$\
  函数的零点与极点的关系为（可去极点当做解析点看待）：\
  $ z_0\是f(z)\的m\阶\极\点<==>z_0\是1/f(z)\的m\阶\零\点 $
]

#def(
  "有限孤立奇点处的留数"
)[\
  设$z_0$是解析函数$f(z)$的有限孤立奇点，把$f(z)$在$z_0$处的洛朗展开式中的\ 负一次幂的系数$C_(-1)$称为$f(z)$在$z_0$处的留数，记作$Res[f(z),z_0]=C_(-1)$\
  易知若$z_0$为$f(z)$的有限可去奇点，则$Res[f(z),z_0]=0$
]

#thm(
  "函数在有限极点处的留数"
)[\
  若$z_0$为$f(z)$的$m(m in NN_+)$阶极点，则
  $ Res[f(z),z_0]=1/(m-1)!lim_(z->z_0)d^(m-1)/(d z^(m-1))[(z-z_0)^m f(z)] $
  其中当$m=1$时，即$z_0$为简单极点时
  $ Res[f(z),z_0]=lim_(z->z_0)[(z-z_0)f(z)] $
  设$f(z)=(P(z))/(Q(z))$，其中$P(z)$与$Q(z)$在$z_0$处均解析，\ 若$P(z_0)!=0$，$z_0$为$Q(z)$的一阶零点，则$z_0$为$f(z)$的一阶极点，且
  $ Res[f(z),z_0]=(P(z_0))/(Q'(z_0)) $
]

#thm(
  "函数在无穷远点的留数"
)[\
  $ Res[f(z),infinity]=-C_(-1)=-Res[f(1/z)1/z^2,0] $
]

#meth(
  "使用留数计算复积分"
)[\
  设函数$f(z)$在区域$D$内除有限个孤立奇点$z_1,z_2,...,z_n$外处处解析，\ $C$是$D$内包围各奇点的一条正向简单闭曲线，则
  $ integral.cont_C f(z)d z=2pi i sum_(k=1)^n Res[f(z),z_k] $
]

#meth(
  "使用留数计算实积分：情形1"
)[\ 
  对于形如$integral_0^(2pi)R(cos theta,sin theta)d theta$的积分，令$z=e^(i theta),d z=i e^(i theta)d theta$，则
  $ sin theta=(e^(i theta)-e^(-i theta))/(2i)=(z^2-1)/(2i z), cos theta=(e^(i theta)+e^(-i theta))/2=(z^2+1)/(2z) $
  $ \记f(z)=R((z^2+1)/(2z),(z^2-1)/(2i z))1/(i z) $
  设$f(z)$在积分闭路$|z|=1$上无奇点，在$|z|<1$内有$n$个奇点$z_1,z_2,...,z_n$,
  $ integral_0^(2pi)R(cos theta,sin theta)d theta=integral.cont_(|z|=1)f(z)d z=2pi i sum_(k=1)^n Res[f(z),z_k] $
]

#meth(
  "使用留数计算实积分：情形2"
)[\
  对于形如$integral_(-infinity)^(+infinity)R(x)d x$的积分，令
  $ R(z)=P(z)/Q(z)=(a_0z^n+a_1z^(n-1)+dots.c+a_n)/(b_0z^m+b_1z^(m-1)+dots.c+b_m),(a_0b_0!=0,m-n>=2) $
  其中$Q(z)$在实轴上无零点，记$R(z)$在上半平面内的极点$z_1,z_2,...,z_n$
  $ integral_(-infinity)^(+infinity)R(x)d x=2pi i sum_(k=1)^n Res[R(z),z_k] $
  如果$R(x)$为偶函数，则
  $ integral_0^(+infinity)R(x)d x=1/2integral_(-infinity)^(+infinity)R(x)d x=pi i sum_(k=1)^(n)Res[R(z),z_k] $
]

#meth(
  "使用留数计算实积分：情形3"
)[\
  对于形如$integral_(-infinity)^(+infinity)R(x)e^(i a x)d x$的积分，当$R(x)$是真分式且在实轴上无零点时，记$f(z)=R(z)e^(i a x)$，其在上半平面的极点为$z_1,z_2,...,z_n$，则
  $ integral_(-infinity)^(+infinity)R(x)e^(i a x)d x=2pi i sum_(k=1)^n Res[f(z),z_k] $
  $ integral_(-infinity)^(+infinity)R(x)cos(a x)d x=Re(2pi i sum_(k=1)^n Res[f(z),z_k]) $
  $ integral_(-infinity)^(+infinity)R(x)sin(a x)d x=Im(2pi i sum_(k=1)^n Res[f(z),z_k]) $
]

= Fourier变换与Laplace变换

#thm(
  "傅里叶变换的对称性"
)[\
  已知$cal(F)[f(t)]=F(omega)$，则
  $ cal(F)[F(t)]=2pi f(-omega) $
  $ cal(F)^(-1)[f(omega)]=1/(2pi)F(-t) $
]

#thm(
  "傅里叶变换表（补充）"
)[\
  $ 2u(t)-1=sgn(t) <--> 2/(j w) $
  $ cos(omega_0t) <--> pi[delta(omega-omega_0)+delta(omega+omega_0)] $
  $ sin(omega_0t) <--> j pi[delta(omega+omega_0)-delta(omega-omega_0)] $
  $ delta(t+a) <--> e^(j a omega) $
  $ 1/(2j)[delta(t+a)-delta(t-a)] <--> sin(a omega)=(e^(j a omega)-e^(-j a omega))/(2j) $
  $ 1/2[delta(t+a)+delta(t-a)] <--> cos(a omega)=(e^(j a omega)+e^(-j a omega))/2 $
]

#thm(
  "三角函数公式（补充）"
)[\ 
  $ sin(3alpha)=3sin alpha-4sin^3alpha $
  $ cos(3alpha)=-3cos alpha+4cos^3alpha $
  $ sin alpha+sin beta=2sin (alpha+beta)/2cos (alpha-beta)/2 $
  $ sin alpha-sin beta=2cos (alpha+beta)/2sin (alpha-beta)/2 $
  $ cos alpha+cos beta=2cos (alpha+beta)/2cos (alpha-beta)/2 $
  $ cos alpha-cos beta=-2sin (alpha+beta)/2sin (alpha-beta)/2 $
]

#thm(
  "Parseval等式"
)[\
  $ integral_(-infinity)^(+infinity)f^2(t)d t=1/(2pi)integral_(-infinity)^(+infinity)|F(omega)|^2d omega $
]

#thm(
  "利用留数计算Laplace逆变换"
)[\
  设$F(s)$除在半平面$Re s<=c$内有有限个有限孤立奇点$s_1,s_2,...,s_n$外\ 是解析的，且当$s->infinity$时$F(s)->0$，则有：$(t>0)$
  $ f(t)=cal(L)^(-1)[F(s)]=sum_(k=1)^n Res[F(s)e^(s t),s_k] $
]

= 常用积分

== 不定积分（C省略）

$ integral x sin((\npi x)/l)\dx = l/(n pi)[-x cos((n pi x)/l)+l/(n pi) sin((n pi x)/l)] $
$ integral x cos((\npi x)/l)\dx = l/(n pi)[x sin((n pi x)/l)+l/(n pi) cos((n pi x)/l)] $
$ integral x^2 sin((\npi x)/l)\dx = l/(n pi){-x^2 cos((\npi x)/l)+(2l)/(n pi)[x sin((\npi x)/l)+l/(n pi)cos((\npi x)/l)]} $
$ integral x^2 cos((\npi x)/l)\dx = l/(n pi){x^2 sin((\npi x)/l)+(2l)/(n pi)[x cos((\npi x)/l)-l/(n pi)sin((\npi x)/l)]} $
$ integral e^(a x)cos(b x)d x=e^(a x)/(a^2+b^2)[a cos(b x)+b sin(b x)] $
$ integral e^(a x)sin(b x)d x=e^(a x)/(a^2+b^2)[-b cos(b x)+a sin(b x)] $

== 定积分

$ integral_0^l x sin((\npi x)/l)\dx = l^2/(n pi)(-1)^(n+1) $
$ integral_0^l x cos((\npi x)/l)\dx = l^2/(n pi)^2 [(-1)^n-1] $
$ integral_0^l x^2 sin((\npi x)/l)\dx = l^3/(n pi)(-1)^(n+1)+(2l^3)/(n pi)^3[(-1)^(n)-1] $
$ integral_0^l x^2 cos((\npi x)/l)\dx = (2l^3)/(n pi)^3(-1)^n $
$ integral_0^l x sin[((2n+1)pi x)/(2l)]\dx=(4l^2)/((2n+1)^2pi^2)(-1)^n $
$ integral_0^l x cos[((2n+1)pi x)/(2l)]\dx=(-1)^n (2l^2)/((2n+1)pi)-(4l^2)/((2n+1)^2pi^2) $

= 分离变量法

== 傅里叶级数

#thm(
  "傅里叶级数系数"
)[\
  $ f(x)~a_0/2+sum_(n=1)^infinity (a_n cos (n pi)/l x+b_n sin (n pi)/l x) $
  $ a_n=1/l integral_(-l)^l f(x)cos((n pi)/l x) d x $
  $ b_n=1/l integral_(-l)^l f(x)sin((n pi)/l x) d x $
]

#thm(
  "形式正弦、形式余弦傅里叶级数系数"
)[\
  $ f(x)~sum_(n=1)^infinity b_n sin (n pi)/l x $
  $ b_n=2/l integral_0^l f(x)sin((n pi)/l x) d x $
  $ f(x)~a_0/2+sum_(n=1)^infinity a_n cos (n pi)/l x $
  $ a_n=2/l integral_0^l f(x)cos((n pi)/l x) d x $
]

== 常见ODE解的讨论

#case(
  $X''+lambda X = 0$
)[\
  $X(0)=X(l)=0 ==>X = sin((k pi x)/l)$\
  $X'(0)=X(l)=0 ==>X = cos(((2k+1) pi x)/(2l))$\
  $X(0)=X'(l)=0 ==>X = sin(((2k+1) pi x)/(2l))$\
  $X'(0)=X'(l)=0 ==>X = cos((k pi x)/l)$
]

#case(
  $x^2y''+a_1x y'+a_2y=f(x)$
)[\
  一般采用换元：$x = e^t,(d y)/(d t) = x (d y)/(d x)$\
  对于$x^2y''+a_1x y'+a_2y=0$，可设$y=x^k$代入求解\
  对于$x^2y''+x y'-n^2y=0$，分以下两种情况：\
  $n=0 ==> y=c_1+c_2ln x$\
  $n>0 ==> y=c_1x^(-n)+c_2x^n$
]

#case(
  $x^2y''+x y'+(beta^2x^2-n^2)y=0$
)[\
  $y = c_1 J_n (beta x)+c_2Y_n (beta x)$
]

#meth(
  "常数易变法"
)[\
  已知其次方程$y''+a y'+ b y = 0$的解是$y_1 ,y_2$\
  那么$y''+a y'+ b y = f(x)$的特解$y = c_1(x)y_1+c_2(x)y_2,$其中
  $ cases(
    c'_1 y_1+c'_2 y_2 = 0,
    c'_1y'_1+c'_2y'_2=f) $
  也可直接通过下式求出$y$：
  $ y=integral_(x_0)^x (y_2(x)y_1(t)-y_1(x)y_2(t))/(y_1(t)y_2 '(t)-y_2(t)y_1 '(t))f(t)d t $
]

= 贝塞尔函数

#meth(
  "在贝塞尔函数系下展开"
)[\
  $ f(r)=sum_(k=1)^(infinity)A_k J_n (mu_k^((n))/R r) $
  $ A_k=1/(R^2/2J_(n-1)^2(mu^((n))_k))integral_0^R r f(r) J_n (mu_k^((n))/R r)d r $
  常见的展开有：
  $ 1 = sum_(m=1)^(+infinity)2/(mu_m^((0))J_1(mu_m^((0))))J_0(mu_m^((0))/R r) $
  $ r^2 = sum_(m=1)^(+infinity)[(2R^2)/(mu_m^((0))J_1(mu_m^((0))))-(4R^2J_2(mu_m^((0))))/((mu_m^((0)))^2J_1^2(mu_m^((0))))]J_0(mu_m^((n))/R r) \ =sum_(m=1)^(+infinity)[(2R^2)/(mu_m^((0))J_1(mu_m^((0))))-(8R^2)/((mu_m^((0)))^3J_1(mu_m^((0))))]J_0(mu_m^((n))/R r) $
]

#thm(
  "贝塞尔正交函数系（补充）"
)[\
  若$lambda_i (i=1,2,3,...)$是$J_1(x)$的正零点，则函数系
  $ {1,J_0(lambda_i/R x):i=1,2,3,...} $
  在$[0,R]$上是带权函数$x$的完全的正交函数系，且
  $ integral_0^R x J_0(lambda_i/R x)J_0(lambda_j/R x)d x=cases(
    0\, & space.quad & i!=j,
    R^2/2J_0^2(lambda_i)\, && i=j
  ) $
]

#thm(
  "半奇数阶的贝塞尔函数展开式"
)[\
  $ J_(n+1/2)(x)=(-1)^n sqrt(2/pi)x^(n+1/2)(1/x d/(d x))^n ((sin x)/x) $
  $ J_(-(n+1/2))(x)=sqrt(2/pi)x^(n+1/2)(1/x d/(d x))^n ((cos x)/x) $
]

#thm(
  "伽马函数的性质"
)[
  $ Gamma(1)=1,Gamma(1/2)=sqrt(pi),1/Gamma(-n)=0,(n in NN) $
  $ Gamma(m+1)=m Gamma(m) ==> Gamma(m+1)=m!,(m in NN) $
]

= 行波法

#meth(
  "半无界弦振动问题：延拓法"
)[\
  在$x>=0,t>=0$范围内有如下弦振动方程与初值条件：
  $ cases(
    (partial^2u)/(partial t^2)=a^2(partial^2u)/(partial x^2)+f(x,t),
    u(x,0)=phi(x)\, (partial u(x,0))/(partial t)=psi(x)
  ) $
  当$x-a t>=0$时，直接代入达朗贝尔公式即可；当$x-a t<0$时：\
  若补充边界条件$u(0,t)=0$，则对$f,phi,psi$进行奇延拓，最终结果为：
  $ u(x,t)=1/2(phi(a t+x)-phi(a t-x))+1/(2a)integral_(a t-x)^(a t+x)psi(xi)d xi\ +1/(2a)[integral_0^(t-x/a)integral_(a(t-tau)-x)^(a(t-tau)+x)f(xi,tau)d xi d tau+integral_(t-x/a)^t integral_(x-a(t-tau))^(x+a(t-tau))f(xi,tau)d xi d tau] $
  若补充边界条件$(partial u(0,t))/(partial x)=0$，则对$f,phi,psi$进行偶延拓，最终结果为：
  $ u(x,t)=1/2(phi(a t+x)+phi(a t-x))+1/(2a)integral_0^(a t-x)psi(xi)d xi+1/(2a)integral_0^(a t+x)psi(xi)d xi\ +1/(2a){integral_0^(t-x/a)[integral_0^(a(t-tau)-x)f(xi,tau)d xi+integral_0^(a(t-tau)+x)f(xi,tau)d xi]d tau+integral_(t-x/a)^t integral_(x-a(t-tau))^(x+a(t-tau))f(xi,tau)d xi d tau} $
]

#meth(
  "半无界弦振动问题：行波法"
)[\
  在$x>=0,t>=0$范围内有如下弦振动方程与初值条件：
  $ cases(
    (partial^2u)/(partial t^2)=a^2(partial^2u)/(partial x^2),
    u(x,0)=phi(x)\, (partial u(x,0))/(partial t)=psi(x)
  ) $
  设解为$u=f_1(x+a t)+f_2(x-a t)$，代入初值条件可得如下方程组：
  $ cases(
    f_1(x)+f_2(x)=phi(x),
    a(f_1 '(x)-f_2 '(x))=psi(x)
  ) $
  求解可得到$x>=0$情形下的$f_1(x),f_2(x)$；接着考虑$x<0$情形下的$f_2(x)$：
  若补充边界条件$u(0,t)=h(t)$，则可得到如下方程：
  $ f_1(a t)+f_2(-a t)=h(t) $
  若补充边界条件$(partial u(0,t))/(partial x)=h(t)$，则可得到如下方程：
  $ f_1 '(a t)+f_2 '(-a t)=h(t) $
]