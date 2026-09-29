-- Prove2me | solution 1 for EmlComplexity.exp_bounds_one_two
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T08:07:19.515873+00:00
-- url     : https://prove2.me/submissions/95517b68-7a0c-4748-ab34-0d81bfd13461

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace EmlComplexity.ExpBoundsProof_one_two
lemma scaled_bounds (x r b e lo hi:ℝ) (n:ℕ)
   (hx:x = n * r) (he:|Real.exp r - b|≤e)
   (hb:0≤b - e) (hl:lo≤(b-e)^n) (hu:(b+e)^n≤hi) :
   lo≤Real.exp x∧Real.exp x≤hi:=by
 have he':=abs_sub_le_iff.mp he
 have hb':b-e≤Real.exp r:=by linarith
 have he'':Real.exp r≤b+e:=by linarith
 rw [hx,Real.exp_nat_mul]
 constructor
 · exact le_trans hl (pow_le_pow_left₀ hb hb' n)
 · exact le_trans (pow_le_pow_left₀ (Real.exp_pos r).le he'' n) hu
lemma scaled_interval (x r l u lo hi:ℝ) (n:ℕ)
   (hx:x = n*r) (h:l≤Real.exp r∧Real.exp r≤u)
   (hp:0≤l) (hl:lo≤l^n) (hu:u^n≤hi) :
   lo≤Real.exp x∧Real.exp x≤hi:=by
 rw [hx,Real.exp_nat_mul]
 exact ⟨le_trans hl (pow_le_pow_left₀ hp h.1 n),
   le_trans (pow_le_pow_left₀ (Real.exp_pos r).le h.2 n) hu⟩
lemma p0:(67957/25000:ℝ)≤Real.exp (1:ℝ)∧Real.exp (1:ℝ)≤(271829/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(1/2:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1/2:ℝ)) (l:=(1648721/1000000:ℝ)) (u:=(824361/500000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p3:(557493/100000:ℝ)≤Real.exp (42957/25000:ℝ)∧Real.exp (42957/25000:ℝ)≤(278747/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(42957/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(42957/100000:ℝ)) (l:=(76829829/50000000:ℝ)) (u:=(30731933/20000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p17:(457487/100000:ℝ)≤Real.exp (76029/50000:ℝ)∧Real.exp (76029/50000:ℝ)≤(28593/6250:ℝ):=by
 have h:=Real.exp_bound (x:=(76029/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(76029/200000:ℝ)) (l:=(146249613/100000000:ℝ)) (u:=(73124833/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p20:(87013/12500:ℝ)≤Real.exp (194033/100000:ℝ)∧Real.exp (194033/100000:ℝ)≤(139221/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(194033/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(194033/400000:ℝ)) (l:=(40607721/25000000:ℝ)) (u:=(81215451/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p25:(67527/12500:ℝ)≤Real.exp (4217/2500:ℝ)∧Real.exp (4217/2500:ℝ)≤(540217/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(4217/10000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(4217/10000:ℝ)) (l:=(152455103/100000000:ℝ)) (u:=(15245511/10000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p31:(278749/50000:ℝ)≤Real.exp (171829/100000:ℝ)∧Real.exp (171829/100000:ℝ)≤(557499/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(171829/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(171829/400000:ℝ)) (l:=(76830021/50000000:ℝ)) (u:=(153660049/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p32:(228753/50000:ℝ)≤Real.exp (76031/50000:ℝ)∧Real.exp (76031/50000:ℝ)≤(457507/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(76031/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(76031/200000:ℝ)) (l:=(146251123/100000000:ℝ)) (u:=(146251127/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p37:(62919/12500:ℝ)≤Real.exp (40403/25000:ℝ)∧Real.exp (40403/25000:ℝ)≤(503353/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(40403/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(40403/100000:ℝ)) (l:=(37446221/25000000:ℝ)) (u:=(149784889/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p38:(285659/100000:ℝ)≤Real.exp (104963/100000:ℝ)∧Real.exp (104963/100000:ℝ)≤(14283/5000:ℝ):=by
 have h:=Real.exp_bound (x:=(104963/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(104963/400000:ℝ)) (l:=(130005617/100000000:ℝ)) (u:=(130005621/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p45:(66247/20000:ℝ)≤Real.exp (59883/50000:ℝ)∧Real.exp (59883/50000:ℝ)≤(82809/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(59883/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(59883/200000:ℝ)) (l:=(134906927/100000000:ℝ)) (u:=(67453469/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p49:(145859/50000:ℝ)≤Real.exp (53531/50000:ℝ)∧Real.exp (53531/50000:ℝ)≤(291719/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(53531/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(53531/200000:ℝ)) (l:=(65344807/50000000:ℝ)) (u:=(130689619/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p57:(135077/25000:ℝ)≤Real.exp (168697/100000:ℝ)∧Real.exp (168697/100000:ℝ)≤(540309/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(168697/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(168697/400000:ℝ)) (l:=(152461583/100000000:ℝ)) (u:=(152461589/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p58:(301567/50000:ℝ)≤Real.exp (179697/100000:ℝ)∧Real.exp (179697/100000:ℝ)≤(120627/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(179697/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(179697/400000:ℝ)) (l:=(78356227/50000000:ℝ)) (u:=(31342493/20000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p59:(86783/20000:ℝ)≤Real.exp (9173/6250:ℝ)∧Real.exp (9173/6250:ℝ)≤(108479/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(9173/25000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(9173/25000:ℝ)) (l:=(72164103/50000000:ℝ)) (u:=(144328247/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p61:(41649/12500:ℝ)≤Real.exp (24071/20000:ℝ)∧Real.exp (24071/20000:ℝ)≤(333193/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(24071/80000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(24071/80000:ℝ)) (l:=(33776431/25000000:ℝ)) (u:=(27021147/20000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p69:(503377/100000:ℝ)≤Real.exp (161617/100000:ℝ)∧Real.exp (161617/100000:ℝ)≤(251689/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(161617/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(161617/400000:ℝ)) (l:=(37446689/25000000:ℝ)) (u:=(149786761/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p71:(71419/25000:ℝ)≤Real.exp (104969/100000:ℝ)∧Real.exp (104969/100000:ℝ)≤(285677/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(104969/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(104969/400000:ℝ)) (l:=(130007567/100000000:ℝ)) (u:=(32501893/25000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p85:(47969/10000:ℝ)≤Real.exp (156797/100000:ℝ)∧Real.exp (156797/100000:ℝ)≤(479691/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(156797/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(156797/400000:ℝ)) (l:=(73996329/50000000:ℝ)) (u:=(73996331/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p86:(73121/25000:ℝ)≤Real.exp (26831/25000:ℝ)∧Real.exp (26831/25000:ℝ)≤(58497/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(26831/100000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(26831/100000:ℝ)) (l:=(130775243/100000000:ℝ)) (u:=(130775249/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p87:(385657/100000:ℝ)≤Real.exp (67489/50000:ℝ)∧Real.exp (67489/50000:ℝ)≤(192829/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(67489/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(67489/200000:ℝ)) (l:=(140136231/100000000:ℝ)) (u:=(28027251/20000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p91:(305043/50000:ℝ)≤Real.exp (180843/100000:ℝ)∧Real.exp (180843/100000:ℝ)≤(610087/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(180843/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(180843/400000:ℝ)) (l:=(157162079/100000000:ℝ)) (u:=(15716209/10000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p93:(119219/20000:ℝ)≤Real.exp (178523/100000:ℝ)∧Real.exp (178523/100000:ℝ)≤(18628/3125:ℝ):=by
 have h:=Real.exp_bound (x:=(178523/400000:ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(178523/400000:ℝ)) (l:=(78126593/50000000:ℝ)) (u:=(39063297/25000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p97:(36467/12500:ℝ)≤Real.exp (26767/25000:ℝ)∧Real.exp (26767/25000:ℝ)≤(291737/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(26767/100000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(26767/100000:ℝ)) (l:=(65345787/50000000:ℝ)) (u:=(130691579/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p98:(737259/100000:ℝ)≤Real.exp (199777/100000:ℝ)∧Real.exp (199777/100000:ℝ)≤(36863/5000:ℝ):=by
 have h:=Real.exp_bound (x:=(199777/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(199777/400000:ℝ)) (l:=(32956043/20000000:ℝ)) (u:=(82390119/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p99:(280473/100000:ℝ)≤Real.exp (103131/100000:ℝ)∧Real.exp (103131/100000:ℝ)≤(140237/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(103131/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(103131/400000:ℝ)) (l:=(129411553/100000000:ℝ)) (u:=(129411557/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p104:(301051/100000:ℝ)≤Real.exp (110211/100000:ℝ)∧Real.exp (110211/100000:ℝ)≤(75263/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(110211/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(110211/400000:ℝ)) (l:=(131722527/100000000:ℝ)) (u:=(65861267/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p105:(132617/25000:ℝ)≤Real.exp (166859/100000:ℝ)∧Real.exp (166859/100000:ℝ)≤(530469/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(166859/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(166859/400000:ℝ)) (l:=(151762629/100000000:ℝ)) (u:=(30352527/20000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p119:(282077/100000:ℝ)≤Real.exp (103701/100000:ℝ)∧Real.exp (103701/100000:ℝ)≤(141039/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(103701/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(103701/400000:ℝ)) (l:=(129596099/100000000:ℝ)) (u:=(1295961/1000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p121:(21139/6250:ℝ)≤Real.exp (60927/50000:ℝ)∧Real.exp (60927/50000:ℝ)≤(13529/4000:ℝ):=by
 have h:=Real.exp_bound (x:=(60927/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(60927/200000:ℝ)) (l:=(135612981/100000000:ℝ)) (u:=(67806497/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p123:(139369/25000:ℝ)≤Real.exp (6873/4000:ℝ)∧Real.exp (6873/4000:ℝ)≤(557477/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(6873/16000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(6873/16000:ℝ)) (l:=(30731701/20000000:ℝ)) (u:=(153658513/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p133:(603297/100000:ℝ)≤Real.exp (44931/25000:ℝ)∧Real.exp (44931/25000:ℝ)≤(301649/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(44931/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(44931/100000:ℝ)) (l:=(156723033/100000000:ℝ)) (u:=(156723043/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p136:(433959/100000:ℝ)≤Real.exp (73389/50000:ℝ)∧Real.exp (73389/50000:ℝ)≤(10849/2500:ℝ):=by
 have h:=Real.exp_bound (x:=(73389/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(73389/200000:ℝ)) (l:=(144331851/100000000:ℝ)) (u:=(72165927/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p142:(83303/25000:ℝ)≤Real.exp (120361/100000:ℝ)∧Real.exp (120361/100000:ℝ)≤(333213/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(120361/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(120361/400000:ℝ)) (l:=(540431/400000:ℝ)) (u:=(135107761/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p143:(566077/100000:ℝ)≤Real.exp (43339/25000:ℝ)∧Real.exp (43339/25000:ℝ)≤(283039/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(43339/100000:ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(43339/100000:ℝ)) (l:=(77123883/50000000:ℝ)) (u:=(154247767/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p144:(436723/100000:ℝ)≤Real.exp (147413/100000:ℝ)∧Real.exp (147413/100000:ℝ)≤(109181/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(147413/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(147413/400000:ℝ)) (l:=(3614029/2500000:ℝ)) (u:=(144561163/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p145:(241769/50000:ℝ)≤Real.exp (39399/25000:ℝ)∧Real.exp (39399/25000:ℝ)≤(483539/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(39399/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(39399/100000:ℝ)) (l:=(18536071/12500000:ℝ)) (u:=(148288573/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p148:(156557/50000:ℝ)≤Real.exp (5707/5000:ℝ)∧Real.exp (5707/5000:ℝ)≤(62623/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(5707/20000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(5707/20000:ℝ)) (l:=(26604549/20000000:ℝ)) (u:=(133022753/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p149:(296931/100000:ℝ)≤Real.exp (108833/100000:ℝ)∧Real.exp (108833/100000:ℝ)≤(74233/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(108833/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(108833/400000:ℝ)) (l:=(32817381/25000000:ℝ)) (u:=(13126953/10000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p166:(239857/50000:ℝ)≤Real.exp (78401/50000:ℝ)∧Real.exp (78401/50000:ℝ)≤(95943/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(78401/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(78401/200000:ℝ)) (l:=(36998627/25000000:ℝ)) (u:=(9249657/6250000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p168:(36563/12500:ℝ)≤Real.exp (107331/100000:ℝ)∧Real.exp (107331/100000:ℝ)≤(58501/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(107331/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(107331/400000:ℝ)) (l:=(32694383/25000000:ℝ)) (u:=(130777537/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p170:(96419/25000:ℝ)≤Real.exp (134983/100000:ℝ)∧Real.exp (134983/100000:ℝ)≤(385677/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(134983/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(134983/400000:ℝ)) (l:=(140137983/100000000:ℝ)) (u:=(70069003/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p174:(610147/100000:ℝ)≤Real.exp (180853/100000:ℝ)∧Real.exp (180853/100000:ℝ)≤(152537/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(180853/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(180853/400000:ℝ)) (l:=(19645751/12500000:ℝ)) (u:=(157166019/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p175:(349761/100000:ℝ)≤Real.exp (15651/12500:ℝ)∧Real.exp (15651/12500:ℝ)≤(174881/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(15651/50000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(15651/50000:ℝ)) (l:=(136754887/100000000:ℝ)) (u:=(136754889/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p177:(696139/100000:ℝ)≤Real.exp (97019/50000:ℝ)∧Real.exp (97019/50000:ℝ)≤(34807/5000:ℝ):=by
 have h:=Real.exp_bound (x:=(97019/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(97019/200000:ℝ)) (l:=(81216457/50000000:ℝ)) (u:=(40608233/25000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p178:(149037/25000:ℝ)≤Real.exp (44633/25000:ℝ)∧Real.exp (44633/25000:ℝ)≤(596149/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(44633/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(44633/100000:ℝ)) (l:=(78128347/50000000:ℝ)) (u:=(2441511/1562500:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p179:(21471/4000:ℝ)≤Real.exp (168041/100000:ℝ)∧Real.exp (168041/100000:ℝ)≤(67097/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(168041/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(168041/400000:ℝ)) (l:=(152211751/100000000:ℝ)) (u:=(152211757/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p204:(633449/100000:ℝ)≤Real.exp (184601/100000:ℝ)∧Real.exp (184601/100000:ℝ)≤(12669/2000:ℝ):=by
 have h:=Real.exp_bound (x:=(184601/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(184601/400000:ℝ)) (l:=(158645573/100000000:ℝ)) (u:=(31729117/20000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p205:(245597/50000:ℝ)≤Real.exp (159167/100000:ℝ)∧Real.exp (159167/100000:ℝ)≤(98239/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(159167/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(159167/400000:ℝ)) (l:=(148872117/100000000:ℝ)) (u:=(148872121/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p207:(57859/20000:ℝ)≤Real.exp (26557/25000:ℝ)∧Real.exp (26557/25000:ℝ)≤(18081/6250:ℝ):=by
 have h:=Real.exp_bound (x:=(26557/100000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(26557/100000:ℝ)) (l:=(13041741/10000000:ℝ)) (u:=(26083483/20000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p208:(152713/50000:ℝ)≤Real.exp (55827/50000:ℝ)∧Real.exp (55827/50000:ℝ)≤(305427/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(55827/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(55827/200000:ℝ)) (l:=(264397/200000:ℝ)) (u:=(660993/500000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p209:(202713/50000:ℝ)≤Real.exp (139977/100000:ℝ)∧Real.exp (139977/100000:ℝ)≤(405427/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(139977/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(139977/400000:ℝ)) (l:=(141898567/100000000:ℝ)) (u:=(141898597/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p210:(33979/10000:ℝ)≤Real.exp (30579/25000:ℝ)∧Real.exp (30579/25000:ℝ)≤(339791/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(30579/100000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(30579/100000:ℝ)) (l:=(27153941/20000000:ℝ)) (u:=(135769717/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p212:(308457/50000:ℝ)≤Real.exp (45489/25000:ℝ)∧Real.exp (45489/25000:ℝ)≤(123383/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(45489/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(45489/100000:ℝ)) (l:=(157599991/100000000:ℝ)) (u:=(78800001/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p213:(88761/12500:ℝ)≤Real.exp (98011/50000:ℝ)∧Real.exp (98011/50000:ℝ)≤(710089/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(98011/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(98011/200000:ℝ)) (l:=(163240581/100000000:ℝ)) (u:=(163240601/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p217:(320981/50000:ℝ)≤Real.exp (11621/6250:ℝ)∧Real.exp (11621/6250:ℝ)≤(641963/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(11621/25000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(11621/25000:ℝ)) (l:=(621781/390625:ℝ)) (u:=(3183519/2000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p218:(42427/10000:ℝ)≤Real.exp (3613/2500:ℝ)∧Real.exp (3613/2500:ℝ)≤(424271/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(3613/10000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(3613/10000:ℝ)) (l:=(143519393/100000000:ℝ)) (u:=(35879849/25000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p220:(680971/100000:ℝ)≤Real.exp (38367/20000:ℝ)∧Real.exp (38367/20000:ℝ)≤(170243/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(38367/80000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(38367/80000:ℝ)) (l:=(6461631/4000000:ℝ)) (u:=(20192599/12500000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p229:(82813/25000:ℝ)≤Real.exp (119771/100000:ℝ)∧Real.exp (119771/100000:ℝ)≤(331253/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(119771/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(119771/400000:ℝ)) (l:=(67454307/50000000:ℝ)) (u:=(8431789/6250000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p230:(70131/25000:ℝ)≤Real.exp (103149/100000:ℝ)∧Real.exp (103149/100000:ℝ)≤(11221/4000:ℝ):=by
 have h:=Real.exp_bound (x:=(103149/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(103149/400000:ℝ)) (l:=(4044293/3125000:ℝ)) (u:=(129417381/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p231:(17631/6250:ℝ)≤Real.exp (25927/25000:ℝ)∧Real.exp (25927/25000:ℝ)≤(282097/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(25927/100000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(25927/100000:ℝ)) (l:=(129598363/100000000:ℝ)) (u:=(4049949/3125000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p232:(271833/100000:ℝ)≤Real.exp (50001/50000:ℝ)∧Real.exp (50001/50000:ℝ)≤(135917/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(50001/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(50001/200000:ℝ)) (l:=(128403181/100000000:ℝ)) (u:=(8025199/6250000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p236:(43651/12500:ℝ)≤Real.exp (2501/2000:ℝ)∧Real.exp (2501/2000:ℝ)≤(349209/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(2501/8000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(2501/8000:ℝ)) (l:=(34175217/25000000:ℝ)) (u:=(68350441/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p237:(597097/100000:ℝ)≤Real.exp (178691/100000:ℝ)∧Real.exp (178691/100000:ℝ)≤(298549/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(178691/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(178691/400000:ℝ)) (l:=(78159409/50000000:ℝ)) (u:=(39079707/25000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p238:(56849/12500:ℝ)≤Real.exp (151467/100000:ℝ)∧Real.exp (151467/100000:ℝ)≤(454793/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(151467/400000:ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(151467/400000:ℝ)) (l:=(146033739/100000000:ℝ)) (u:=(7301687/5000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p242:(3574/625:ℝ)≤Real.exp (174369/100000:ℝ)∧Real.exp (174369/100000:ℝ)≤(571841/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(174369/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(174369/400000:ℝ)) (l:=(154638887/100000000:ℝ)) (u:=(30927779/20000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p250:(315901/100000:ℝ)≤Real.exp (57513/50000:ℝ)∧Real.exp (57513/50000:ℝ)≤(157951/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(57513/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(57513/200000:ℝ)) (l:=(133317717/100000000:ℝ)) (u:=(5332709/4000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p251:(103617/20000:ℝ)≤Real.exp (164497/100000:ℝ)∧Real.exp (164497/100000:ℝ)≤(259043/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(164497/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(164497/400000:ℝ)) (l:=(18858639/12500000:ℝ)) (u:=(75434559/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p252:(15717/4000:ℝ)≤Real.exp (27369/20000:ℝ)∧Real.exp (27369/20000:ℝ)≤(196463/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(27369/80000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(27369/80000:ℝ)) (l:=(35197961/25000000:ℝ)) (u:=(14079187/10000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p268:(519449/100000:ℝ)≤Real.exp (4119/2500:ℝ)∧Real.exp (4119/2500:ℝ)≤(10389/2000:ℝ):=by
 have h:=Real.exp_bound (x:=(4119/10000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(4119/10000:ℝ)) (l:=(150968341/100000000:ℝ)) (u:=(150968347/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p287:(27207/4000:ℝ)≤Real.exp (95859/50000:ℝ)∧Real.exp (95859/50000:ℝ)≤(42511/6250:ℝ):=by
 have h:=Real.exp_bound (x:=(95859/200000:ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(95859/200000:ℝ)) (l:=(80746773/50000000:ℝ)) (u:=(40373387/25000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p290:(286933/100000:ℝ)≤Real.exp (3294/3125:ℝ)∧Real.exp (3294/3125:ℝ)≤(143467/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(1647/6250:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1647/6250:ℝ)) (l:=(16268791/12500000:ℝ)) (u:=(130150333/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p292:(167993/50000:ℝ)≤Real.exp (12119/10000:ℝ)∧Real.exp (12119/10000:ℝ)≤(335987/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(12119/40000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(12119/40000:ℝ)) (l:=(135388051/100000000:ℝ)) (u:=(135388063/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p294:(3089/1000:ℝ)≤Real.exp (22557/20000:ℝ)∧Real.exp (22557/20000:ℝ)≤(308901/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(22557/80000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(22557/80000:ℝ)) (l:=(66286447/50000000:ℝ)) (u:=(132572901/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p296:(694443/100000:ℝ)≤Real.exp (96897/50000:ℝ)∧Real.exp (96897/50000:ℝ)≤(173611/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(96897/200000:ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(96897/200000:ℝ)) (l:=(40583469/25000000:ℝ)) (u:=(81166939/50000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p306:(486443/100000:ℝ)≤Real.exp (31639/20000:ℝ)∧Real.exp (31639/20000:ℝ)≤(121611/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(31639/80000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(31639/80000:ℝ)) (l:=(148510797/100000000:ℝ)) (u:=(148510801/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p309:(292463/100000:ℝ)≤Real.exp (107317/100000:ℝ)∧Real.exp (107317/100000:ℝ)≤(18279/6250:ℝ):=by
 have h:=Real.exp_bound (x:=(107317/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(107317/400000:ℝ)) (l:=(1307729/1000000:ℝ)) (u:=(130773/100000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p313:(27183/10000:ℝ)≤Real.exp (100001/100000:ℝ)∧Real.exp (100001/100000:ℝ)≤(271831/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(100001/400000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(100001/400000:ℝ)) (l:=(128402787/100000000:ℝ)) (u:=(32100717/25000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p316:(144193/50000:ℝ)≤Real.exp (105913/100000:ℝ)∧Real.exp (105913/100000:ℝ)≤(288387/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(105913/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(105913/400000:ℝ)) (l:=(130314747/100000000:ℝ)) (u:=(509042/390625:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
end EmlComplexity.ExpBoundsProof_one_two

theorem solution :
((67957/25000:ℝ)≤Real.exp (1:ℝ)∧Real.exp (1:ℝ)≤(271829/100000:ℝ)) ∧
((557493/100000:ℝ)≤Real.exp (42957/25000:ℝ)∧Real.exp (42957/25000:ℝ)≤(278747/50000:ℝ)) ∧
((457487/100000:ℝ)≤Real.exp (76029/50000:ℝ)∧Real.exp (76029/50000:ℝ)≤(28593/6250:ℝ)) ∧
((87013/12500:ℝ)≤Real.exp (194033/100000:ℝ)∧Real.exp (194033/100000:ℝ)≤(139221/20000:ℝ)) ∧
((67527/12500:ℝ)≤Real.exp (4217/2500:ℝ)∧Real.exp (4217/2500:ℝ)≤(540217/100000:ℝ)) ∧
((278749/50000:ℝ)≤Real.exp (171829/100000:ℝ)∧Real.exp (171829/100000:ℝ)≤(557499/100000:ℝ)) ∧
((228753/50000:ℝ)≤Real.exp (76031/50000:ℝ)∧Real.exp (76031/50000:ℝ)≤(457507/100000:ℝ)) ∧
((62919/12500:ℝ)≤Real.exp (40403/25000:ℝ)∧Real.exp (40403/25000:ℝ)≤(503353/100000:ℝ)) ∧
((285659/100000:ℝ)≤Real.exp (104963/100000:ℝ)∧Real.exp (104963/100000:ℝ)≤(14283/5000:ℝ)) ∧
((66247/20000:ℝ)≤Real.exp (59883/50000:ℝ)∧Real.exp (59883/50000:ℝ)≤(82809/25000:ℝ)) ∧
((145859/50000:ℝ)≤Real.exp (53531/50000:ℝ)∧Real.exp (53531/50000:ℝ)≤(291719/100000:ℝ)) ∧
((135077/25000:ℝ)≤Real.exp (168697/100000:ℝ)∧Real.exp (168697/100000:ℝ)≤(540309/100000:ℝ)) ∧
((301567/50000:ℝ)≤Real.exp (179697/100000:ℝ)∧Real.exp (179697/100000:ℝ)≤(120627/20000:ℝ)) ∧
((86783/20000:ℝ)≤Real.exp (9173/6250:ℝ)∧Real.exp (9173/6250:ℝ)≤(108479/25000:ℝ)) ∧
((41649/12500:ℝ)≤Real.exp (24071/20000:ℝ)∧Real.exp (24071/20000:ℝ)≤(333193/100000:ℝ)) ∧
((503377/100000:ℝ)≤Real.exp (161617/100000:ℝ)∧Real.exp (161617/100000:ℝ)≤(251689/50000:ℝ)) ∧
((71419/25000:ℝ)≤Real.exp (104969/100000:ℝ)∧Real.exp (104969/100000:ℝ)≤(285677/100000:ℝ)) ∧
((47969/10000:ℝ)≤Real.exp (156797/100000:ℝ)∧Real.exp (156797/100000:ℝ)≤(479691/100000:ℝ)) ∧
((73121/25000:ℝ)≤Real.exp (26831/25000:ℝ)∧Real.exp (26831/25000:ℝ)≤(58497/20000:ℝ)) ∧
((385657/100000:ℝ)≤Real.exp (67489/50000:ℝ)∧Real.exp (67489/50000:ℝ)≤(192829/50000:ℝ)) ∧
((305043/50000:ℝ)≤Real.exp (180843/100000:ℝ)∧Real.exp (180843/100000:ℝ)≤(610087/100000:ℝ)) ∧
((119219/20000:ℝ)≤Real.exp (178523/100000:ℝ)∧Real.exp (178523/100000:ℝ)≤(18628/3125:ℝ)) ∧
((36467/12500:ℝ)≤Real.exp (26767/25000:ℝ)∧Real.exp (26767/25000:ℝ)≤(291737/100000:ℝ)) ∧
((737259/100000:ℝ)≤Real.exp (199777/100000:ℝ)∧Real.exp (199777/100000:ℝ)≤(36863/5000:ℝ)) ∧
((280473/100000:ℝ)≤Real.exp (103131/100000:ℝ)∧Real.exp (103131/100000:ℝ)≤(140237/50000:ℝ)) ∧
((301051/100000:ℝ)≤Real.exp (110211/100000:ℝ)∧Real.exp (110211/100000:ℝ)≤(75263/25000:ℝ)) ∧
((132617/25000:ℝ)≤Real.exp (166859/100000:ℝ)∧Real.exp (166859/100000:ℝ)≤(530469/100000:ℝ)) ∧
((282077/100000:ℝ)≤Real.exp (103701/100000:ℝ)∧Real.exp (103701/100000:ℝ)≤(141039/50000:ℝ)) ∧
((21139/6250:ℝ)≤Real.exp (60927/50000:ℝ)∧Real.exp (60927/50000:ℝ)≤(13529/4000:ℝ)) ∧
((139369/25000:ℝ)≤Real.exp (6873/4000:ℝ)∧Real.exp (6873/4000:ℝ)≤(557477/100000:ℝ)) ∧
((603297/100000:ℝ)≤Real.exp (44931/25000:ℝ)∧Real.exp (44931/25000:ℝ)≤(301649/50000:ℝ)) ∧
((433959/100000:ℝ)≤Real.exp (73389/50000:ℝ)∧Real.exp (73389/50000:ℝ)≤(10849/2500:ℝ)) ∧
((83303/25000:ℝ)≤Real.exp (120361/100000:ℝ)∧Real.exp (120361/100000:ℝ)≤(333213/100000:ℝ)) ∧
((566077/100000:ℝ)≤Real.exp (43339/25000:ℝ)∧Real.exp (43339/25000:ℝ)≤(283039/50000:ℝ)) ∧
((436723/100000:ℝ)≤Real.exp (147413/100000:ℝ)∧Real.exp (147413/100000:ℝ)≤(109181/25000:ℝ)) ∧
((241769/50000:ℝ)≤Real.exp (39399/25000:ℝ)∧Real.exp (39399/25000:ℝ)≤(483539/100000:ℝ)) ∧
((156557/50000:ℝ)≤Real.exp (5707/5000:ℝ)∧Real.exp (5707/5000:ℝ)≤(62623/20000:ℝ)) ∧
((296931/100000:ℝ)≤Real.exp (108833/100000:ℝ)∧Real.exp (108833/100000:ℝ)≤(74233/25000:ℝ)) ∧
((239857/50000:ℝ)≤Real.exp (78401/50000:ℝ)∧Real.exp (78401/50000:ℝ)≤(95943/20000:ℝ)) ∧
((36563/12500:ℝ)≤Real.exp (107331/100000:ℝ)∧Real.exp (107331/100000:ℝ)≤(58501/20000:ℝ)) ∧
((96419/25000:ℝ)≤Real.exp (134983/100000:ℝ)∧Real.exp (134983/100000:ℝ)≤(385677/100000:ℝ)) ∧
((610147/100000:ℝ)≤Real.exp (180853/100000:ℝ)∧Real.exp (180853/100000:ℝ)≤(152537/25000:ℝ)) ∧
((349761/100000:ℝ)≤Real.exp (15651/12500:ℝ)∧Real.exp (15651/12500:ℝ)≤(174881/50000:ℝ)) ∧
((696139/100000:ℝ)≤Real.exp (97019/50000:ℝ)∧Real.exp (97019/50000:ℝ)≤(34807/5000:ℝ)) ∧
((149037/25000:ℝ)≤Real.exp (44633/25000:ℝ)∧Real.exp (44633/25000:ℝ)≤(596149/100000:ℝ)) ∧
((21471/4000:ℝ)≤Real.exp (168041/100000:ℝ)∧Real.exp (168041/100000:ℝ)≤(67097/12500:ℝ)) ∧
((633449/100000:ℝ)≤Real.exp (184601/100000:ℝ)∧Real.exp (184601/100000:ℝ)≤(12669/2000:ℝ)) ∧
((245597/50000:ℝ)≤Real.exp (159167/100000:ℝ)∧Real.exp (159167/100000:ℝ)≤(98239/20000:ℝ)) ∧
((57859/20000:ℝ)≤Real.exp (26557/25000:ℝ)∧Real.exp (26557/25000:ℝ)≤(18081/6250:ℝ)) ∧
((152713/50000:ℝ)≤Real.exp (55827/50000:ℝ)∧Real.exp (55827/50000:ℝ)≤(305427/100000:ℝ)) ∧
((202713/50000:ℝ)≤Real.exp (139977/100000:ℝ)∧Real.exp (139977/100000:ℝ)≤(405427/100000:ℝ)) ∧
((33979/10000:ℝ)≤Real.exp (30579/25000:ℝ)∧Real.exp (30579/25000:ℝ)≤(339791/100000:ℝ)) ∧
((308457/50000:ℝ)≤Real.exp (45489/25000:ℝ)∧Real.exp (45489/25000:ℝ)≤(123383/20000:ℝ)) ∧
((88761/12500:ℝ)≤Real.exp (98011/50000:ℝ)∧Real.exp (98011/50000:ℝ)≤(710089/100000:ℝ)) ∧
((320981/50000:ℝ)≤Real.exp (11621/6250:ℝ)∧Real.exp (11621/6250:ℝ)≤(641963/100000:ℝ)) ∧
((42427/10000:ℝ)≤Real.exp (3613/2500:ℝ)∧Real.exp (3613/2500:ℝ)≤(424271/100000:ℝ)) ∧
((680971/100000:ℝ)≤Real.exp (38367/20000:ℝ)∧Real.exp (38367/20000:ℝ)≤(170243/25000:ℝ)) ∧
((82813/25000:ℝ)≤Real.exp (119771/100000:ℝ)∧Real.exp (119771/100000:ℝ)≤(331253/100000:ℝ)) ∧
((70131/25000:ℝ)≤Real.exp (103149/100000:ℝ)∧Real.exp (103149/100000:ℝ)≤(11221/4000:ℝ)) ∧
((17631/6250:ℝ)≤Real.exp (25927/25000:ℝ)∧Real.exp (25927/25000:ℝ)≤(282097/100000:ℝ)) ∧
((271833/100000:ℝ)≤Real.exp (50001/50000:ℝ)∧Real.exp (50001/50000:ℝ)≤(135917/50000:ℝ)) ∧
((43651/12500:ℝ)≤Real.exp (2501/2000:ℝ)∧Real.exp (2501/2000:ℝ)≤(349209/100000:ℝ)) ∧
((597097/100000:ℝ)≤Real.exp (178691/100000:ℝ)∧Real.exp (178691/100000:ℝ)≤(298549/50000:ℝ)) ∧
((56849/12500:ℝ)≤Real.exp (151467/100000:ℝ)∧Real.exp (151467/100000:ℝ)≤(454793/100000:ℝ)) ∧
((3574/625:ℝ)≤Real.exp (174369/100000:ℝ)∧Real.exp (174369/100000:ℝ)≤(571841/100000:ℝ)) ∧
((315901/100000:ℝ)≤Real.exp (57513/50000:ℝ)∧Real.exp (57513/50000:ℝ)≤(157951/50000:ℝ)) ∧
((103617/20000:ℝ)≤Real.exp (164497/100000:ℝ)∧Real.exp (164497/100000:ℝ)≤(259043/50000:ℝ)) ∧
((15717/4000:ℝ)≤Real.exp (27369/20000:ℝ)∧Real.exp (27369/20000:ℝ)≤(196463/50000:ℝ)) ∧
((519449/100000:ℝ)≤Real.exp (4119/2500:ℝ)∧Real.exp (4119/2500:ℝ)≤(10389/2000:ℝ)) ∧
((27207/4000:ℝ)≤Real.exp (95859/50000:ℝ)∧Real.exp (95859/50000:ℝ)≤(42511/6250:ℝ)) ∧
((286933/100000:ℝ)≤Real.exp (3294/3125:ℝ)∧Real.exp (3294/3125:ℝ)≤(143467/50000:ℝ)) ∧
((167993/50000:ℝ)≤Real.exp (12119/10000:ℝ)∧Real.exp (12119/10000:ℝ)≤(335987/100000:ℝ)) ∧
((3089/1000:ℝ)≤Real.exp (22557/20000:ℝ)∧Real.exp (22557/20000:ℝ)≤(308901/100000:ℝ)) ∧
((694443/100000:ℝ)≤Real.exp (96897/50000:ℝ)∧Real.exp (96897/50000:ℝ)≤(173611/25000:ℝ)) ∧
((486443/100000:ℝ)≤Real.exp (31639/20000:ℝ)∧Real.exp (31639/20000:ℝ)≤(121611/25000:ℝ)) ∧
((292463/100000:ℝ)≤Real.exp (107317/100000:ℝ)∧Real.exp (107317/100000:ℝ)≤(18279/6250:ℝ)) ∧
((27183/10000:ℝ)≤Real.exp (100001/100000:ℝ)∧Real.exp (100001/100000:ℝ)≤(271831/100000:ℝ)) ∧
((144193/50000:ℝ)≤Real.exp (105913/100000:ℝ)∧Real.exp (105913/100000:ℝ)≤(288387/100000:ℝ)) := by
 exact ⟨EmlComplexity.ExpBoundsProof_one_two.p0,⟨EmlComplexity.ExpBoundsProof_one_two.p3,⟨EmlComplexity.ExpBoundsProof_one_two.p17,⟨EmlComplexity.ExpBoundsProof_one_two.p20,⟨EmlComplexity.ExpBoundsProof_one_two.p25,⟨EmlComplexity.ExpBoundsProof_one_two.p31,⟨EmlComplexity.ExpBoundsProof_one_two.p32,⟨EmlComplexity.ExpBoundsProof_one_two.p37,⟨EmlComplexity.ExpBoundsProof_one_two.p38,⟨EmlComplexity.ExpBoundsProof_one_two.p45,⟨EmlComplexity.ExpBoundsProof_one_two.p49,⟨EmlComplexity.ExpBoundsProof_one_two.p57,⟨EmlComplexity.ExpBoundsProof_one_two.p58,⟨EmlComplexity.ExpBoundsProof_one_two.p59,⟨EmlComplexity.ExpBoundsProof_one_two.p61,⟨EmlComplexity.ExpBoundsProof_one_two.p69,⟨EmlComplexity.ExpBoundsProof_one_two.p71,⟨EmlComplexity.ExpBoundsProof_one_two.p85,⟨EmlComplexity.ExpBoundsProof_one_two.p86,⟨EmlComplexity.ExpBoundsProof_one_two.p87,⟨EmlComplexity.ExpBoundsProof_one_two.p91,⟨EmlComplexity.ExpBoundsProof_one_two.p93,⟨EmlComplexity.ExpBoundsProof_one_two.p97,⟨EmlComplexity.ExpBoundsProof_one_two.p98,⟨EmlComplexity.ExpBoundsProof_one_two.p99,⟨EmlComplexity.ExpBoundsProof_one_two.p104,⟨EmlComplexity.ExpBoundsProof_one_two.p105,⟨EmlComplexity.ExpBoundsProof_one_two.p119,⟨EmlComplexity.ExpBoundsProof_one_two.p121,⟨EmlComplexity.ExpBoundsProof_one_two.p123,⟨EmlComplexity.ExpBoundsProof_one_two.p133,⟨EmlComplexity.ExpBoundsProof_one_two.p136,⟨EmlComplexity.ExpBoundsProof_one_two.p142,⟨EmlComplexity.ExpBoundsProof_one_two.p143,⟨EmlComplexity.ExpBoundsProof_one_two.p144,⟨EmlComplexity.ExpBoundsProof_one_two.p145,⟨EmlComplexity.ExpBoundsProof_one_two.p148,⟨EmlComplexity.ExpBoundsProof_one_two.p149,⟨EmlComplexity.ExpBoundsProof_one_two.p166,⟨EmlComplexity.ExpBoundsProof_one_two.p168,⟨EmlComplexity.ExpBoundsProof_one_two.p170,⟨EmlComplexity.ExpBoundsProof_one_two.p174,⟨EmlComplexity.ExpBoundsProof_one_two.p175,⟨EmlComplexity.ExpBoundsProof_one_two.p177,⟨EmlComplexity.ExpBoundsProof_one_two.p178,⟨EmlComplexity.ExpBoundsProof_one_two.p179,⟨EmlComplexity.ExpBoundsProof_one_two.p204,⟨EmlComplexity.ExpBoundsProof_one_two.p205,⟨EmlComplexity.ExpBoundsProof_one_two.p207,⟨EmlComplexity.ExpBoundsProof_one_two.p208,⟨EmlComplexity.ExpBoundsProof_one_two.p209,⟨EmlComplexity.ExpBoundsProof_one_two.p210,⟨EmlComplexity.ExpBoundsProof_one_two.p212,⟨EmlComplexity.ExpBoundsProof_one_two.p213,⟨EmlComplexity.ExpBoundsProof_one_two.p217,⟨EmlComplexity.ExpBoundsProof_one_two.p218,⟨EmlComplexity.ExpBoundsProof_one_two.p220,⟨EmlComplexity.ExpBoundsProof_one_two.p229,⟨EmlComplexity.ExpBoundsProof_one_two.p230,⟨EmlComplexity.ExpBoundsProof_one_two.p231,⟨EmlComplexity.ExpBoundsProof_one_two.p232,⟨EmlComplexity.ExpBoundsProof_one_two.p236,⟨EmlComplexity.ExpBoundsProof_one_two.p237,⟨EmlComplexity.ExpBoundsProof_one_two.p238,⟨EmlComplexity.ExpBoundsProof_one_two.p242,⟨EmlComplexity.ExpBoundsProof_one_two.p250,⟨EmlComplexity.ExpBoundsProof_one_two.p251,⟨EmlComplexity.ExpBoundsProof_one_two.p252,⟨EmlComplexity.ExpBoundsProof_one_two.p268,⟨EmlComplexity.ExpBoundsProof_one_two.p287,⟨EmlComplexity.ExpBoundsProof_one_two.p290,⟨EmlComplexity.ExpBoundsProof_one_two.p292,⟨EmlComplexity.ExpBoundsProof_one_two.p294,⟨EmlComplexity.ExpBoundsProof_one_two.p296,⟨EmlComplexity.ExpBoundsProof_one_two.p306,⟨EmlComplexity.ExpBoundsProof_one_two.p309,⟨EmlComplexity.ExpBoundsProof_one_two.p313,EmlComplexity.ExpBoundsProof_one_two.p316⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms solution
