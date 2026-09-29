-- Prove2me | solution 1 for EmlComplexity.exp_bounds_negative
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T08:07:17.880441+00:00
-- url     : https://prove2.me/submissions/98c54c11-1954-40ef-ad0a-c139ca63c671

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace EmlComplexity.ExpBoundsProof_negative
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
lemma p12:(6829/100000:ℝ)≤Real.exp (-(134199/50000):ℝ)∧Real.exp (-(134199/50000):ℝ)≤(68291/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(134199/400000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(134199/400000):ℝ)) (l:=(71498227/100000000:ℝ)) (u:=(285993/400000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p19:(999/1000:ℝ)≤Real.exp (-(1/1000):ℝ)∧Real.exp (-(1/1000):ℝ)≤(99901/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1/1000):ℝ)) (by norm_num) (n:=3) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1/1000):ℝ)) (l:=(999/1000:ℝ)) (u:=(999001/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p22:(30721/5000000000:ℝ)≤Real.exp (-12:ℝ)∧Real.exp (-12:ℝ)≤(61443/10000000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(3/8):ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(3/8):ℝ)) (l:=(2749157/4000000:ℝ)) (u:=(68728929/100000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p26:(91/2500:ℝ)≤Real.exp (-(331317/100000):ℝ)∧Real.exp (-(331317/100000):ℝ)≤(36401/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(331317/800000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(331317/800000):ℝ)) (l:=(3304521/5000000:ℝ)) (u:=(16522629/25000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p28:(19771/100000:ℝ)≤Real.exp (-(81047/50000):ℝ)∧Real.exp (-(81047/50000):ℝ)≤(4943/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(81047/200000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(81047/200000):ℝ)) (l:=(33341/50000:ℝ)) (u:=(666821/1000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p33:(27067/50000:ℝ)≤Real.exp (-(61369/100000):ℝ)∧Real.exp (-(61369/100000):ℝ)≤(10827/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(61369/200000):ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(61369/200000):ℝ)) (l:=(73576217/100000000:ℝ)) (u:=(9197061/12500000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p41:(47561/50000:ℝ)≤Real.exp (-(1/20):ℝ)∧Real.exp (-(1/20):ℝ)≤(95123/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1/20):ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1/20):ℝ)) (l:=(237807/250000:ℝ)) (u:=(95123/100000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p46:(27/2500000:ℝ)≤Real.exp (-(571797/50000):ℝ)∧Real.exp (-(571797/50000):ℝ)≤(10801/1000000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(571797/1600000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(571797/1600000):ℝ)) (l:=(699511/1000000:ℝ)) (u:=(87439/125000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p47:(57461/1000000:ℝ)≤Real.exp (-(8927/3125):ℝ)∧Real.exp (-(8927/3125):ℝ)≤(28731/500000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(8927/25000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(8927/25000):ℝ)) (l:=(174929/250000:ℝ)) (u:=(699717/1000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p56:(34119/500000:ℝ)≤Real.exp (-(134237/50000):ℝ)∧Real.exp (-(134237/50000):ℝ)≤(68239/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(134237/400000):ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(134237/400000):ℝ)) (l:=(17872859/25000000:ℝ)) (u:=(35745719/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p62:(5273/100000:ℝ)≤Real.exp (-(18391/6250):ℝ)∧Real.exp (-(18391/6250):ℝ)≤(52731/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(18391/50000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(18391/50000):ℝ)) (l:=(34612087/50000000:ℝ)) (u:=(8653027/12500000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p64:(2403/12500:ℝ)≤Real.exp (-(1649/1000):ℝ)∧Real.exp (-(1649/1000):ℝ)≤(769/4000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1649/4000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1649/4000):ℝ)) (l:=(331079/500000:ℝ)) (u:=(8277/12500:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p66:(12037/100000:ℝ)≤Real.exp (-(211717/100000):ℝ)∧Real.exp (-(211717/100000):ℝ)≤(6019/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(211717/800000):ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(211717/800000):ℝ)) (l:=(191869/250000:ℝ)) (u:=(383739/500000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p72:(16543/25000:ℝ)≤Real.exp (-(41291/100000):ℝ)∧Real.exp (-(41291/100000):ℝ)≤(66173/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(41291/100000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(41291/100000):ℝ)) (l:=(661721/1000000:ℝ)) (u:=(661723/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p75:(19449/25000:ℝ)≤Real.exp (-(6277/25000):ℝ)∧Real.exp (-(6277/25000):ℝ)≤(77797/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(6277/25000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(6277/25000):ℝ)) (l:=(19449/25000:ℝ)) (u:=(777961/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p82:(1/1000:ℝ)≤Real.exp (-(345387/50000):ℝ)∧Real.exp (-(345387/50000):ℝ)≤(10001/10000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(345387/800000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(345387/800000):ℝ)) (l:=(324691/500000:ℝ)) (u:=(81173/125000:ℝ)) (n:=16)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p89:(24751/25000:ℝ)≤Real.exp (-(1/100):ℝ)∧Real.exp (-(1/100):ℝ)≤(19801/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1/100):ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1/100):ℝ)) (l:=(990049/1000000:ℝ)) (u:=(19801/20000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p92:(45869/100000:ℝ)≤Real.exp (-(77937/100000):ℝ)∧Real.exp (-(77937/100000):ℝ)≤(4587/10000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(77937/200000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(77937/200000):ℝ)) (l:=(67727/100000:ℝ)) (u:=(677271/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p94:(1767/25000:ℝ)≤Real.exp (-(132479/50000):ℝ)∧Real.exp (-(132479/50000):ℝ)≤(70681/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(132479/400000):ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(132479/400000):ℝ)) (l:=(71806333/100000000:ℝ)) (u:=(35903167/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p96:(90483/100000:ℝ)≤Real.exp (-(1/10):ℝ)∧Real.exp (-(1/10):ℝ)≤(22621/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1/10):ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1/10):ℝ)) (l:=(904837/1000000:ℝ)) (u:=(452419/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p107:(10811/1000000000:ℝ)≤Real.exp (-(571747/50000):ℝ)∧Real.exp (-(571747/50000):ℝ)≤(2703/250000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(571747/1600000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(571747/1600000):ℝ)) (l:=(69953327/100000000:ℝ)) (u:=(34976681/50000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p108:(60407/1000000:ℝ)≤Real.exp (-(35083/12500):ℝ)∧Real.exp (-(35083/12500):ℝ)≤(7551/125000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(35083/100000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(35083/100000):ℝ)) (l:=(70410341/100000000:ℝ)) (u:=(17602593/25000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p109:(68271/10000000000:ℝ)≤Real.exp (-(59473/5000):ℝ)∧Real.exp (-(59473/5000):ℝ)≤(4267/625000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(59473/160000):ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(59473/160000):ℝ)) (l:=(2758227/4000000:ℝ)) (u:=(34477839/50000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p110:(60211/1000000000:ℝ)≤Real.exp (-(194353/20000):ℝ)∧Real.exp (-(194353/20000):ℝ)≤(15053/250000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(194353/640000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(194353/640000):ℝ)) (l:=(36904977/50000000:ℝ)) (u:=(36904983/50000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p111:(15619/100000:ℝ)≤Real.exp (-(5802/3125):ℝ)∧Real.exp (-(5802/3125):ℝ)≤(781/5000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(2901/6250):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(2901/6250):ℝ)) (l:=(314331/500000:ℝ)) (u:=(125733/200000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p112:(11203/5000000:ℝ)≤Real.exp (-(305049/50000):ℝ)∧Real.exp (-(305049/50000):ℝ)≤(22407/10000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(305049/800000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(305049/800000):ℝ)) (l:=(68296523/100000000:ℝ)) (u:=(34148289/50000000:ℝ)) (n:=16)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p114:(69149/1000000000:ℝ)≤Real.exp (-(239481/25000):ℝ)∧Real.exp (-(239481/25000):ℝ)≤(1383/20000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(239481/800000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(239481/800000):ℝ)) (l:=(74129897/100000000:ℝ)) (u:=(18532477/25000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p116:(17937/100000:ℝ)≤Real.exp (-(42957/25000):ℝ)∧Real.exp (-(42957/25000):ℝ)≤(8969/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(42957/100000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(42957/100000):ℝ)) (l:=(162697/250000:ℝ)) (u:=(65079/100000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p118:(9197/25000:ℝ)≤Real.exp (-(99999/100000):ℝ)∧Real.exp (-(99999/100000):ℝ)≤(36789/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(99999/200000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(99999/200000):ℝ)) (l:=(606533/1000000:ℝ)) (u:=(606537/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p131:(92133/100000:ℝ)≤Real.exp (-(8193/100000):ℝ)∧Real.exp (-(8193/100000):ℝ)≤(46067/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(8193/100000):ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(8193/100000):ℝ)) (l:=(230333/250000:ℝ)) (u:=(921337/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p132:(36349/1000000:ℝ)≤Real.exp (-(165729/50000):ℝ)∧Real.exp (-(165729/50000):ℝ)≤(727/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(165729/400000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(165729/400000):ℝ)) (l:=(66078773/100000000:ℝ)) (u:=(66078869/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p135:(3953/20000:ℝ)≤Real.exp (-(81061/50000):ℝ)∧Real.exp (-(81061/50000):ℝ)≤(9883/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(81061/200000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(81061/200000):ℝ)) (l:=(666773/1000000:ℝ)) (u:=(26671/40000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p141:(5413/10000:ℝ)≤Real.exp (-(30689/50000):ℝ)∧Real.exp (-(30689/50000):ℝ)≤(54131/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(30689/100000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(30689/100000):ℝ)) (l:=(735731/1000000:ℝ)) (u:=(183933/250000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p152:(179/4000:ℝ)≤Real.exp (-(62133/20000):ℝ)∧Real.exp (-(62133/20000):ℝ)≤(44751/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(62133/160000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(62133/160000):ℝ)) (l:=(1695469/2500000:ℝ)) (u:=(33909411/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p154:(19479/100000:ℝ)≤Real.exp (-(81791/50000):ℝ)∧Real.exp (-(81791/50000):ℝ)≤(487/2500:ℝ):=by
 have h:=Real.exp_bound (x:=(-(81791/200000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(81791/200000):ℝ)) (l:=(83043/125000:ℝ)) (u:=(132869/200000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p156:(9097/50000:ℝ)≤Real.exp (-(85203/50000):ℝ)∧Real.exp (-(85203/50000):ℝ)≤(3639/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(85203/200000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(85203/200000):ℝ)) (l:=(326553/500000:ℝ)) (u:=(163277/250000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p158:(10577/100000:ℝ)≤Real.exp (-(224647/100000):ℝ)∧Real.exp (-(224647/100000):ℝ)≤(5289/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(224647/800000):ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(224647/800000):ℝ)) (l:=(75517129/100000000:ℝ)) (u:=(75517289/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p161:(15511/100000:ℝ)≤Real.exp (-(186361/100000):ℝ)∧Real.exp (-(186361/100000):ℝ)≤(1939/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(-(186361/400000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(186361/400000):ℝ)) (l:=(39223/62500:ℝ)) (u:=(627571/1000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p163:(45871/100000:ℝ)≤Real.exp (-(19483/25000):ℝ)∧Real.exp (-(19483/25000):ℝ)≤(2867/6250:ℝ):=by
 have h:=Real.exp_bound (x:=(-(19483/50000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(19483/50000):ℝ)) (l:=(677287/1000000:ℝ)) (u:=(84661/125000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p171:(60471/100000:ℝ)≤Real.exp (-(50299/100000):ℝ)∧Real.exp (-(50299/100000):ℝ)≤(7559/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(-(50299/200000):ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(50299/200000):ℝ)) (l:=(77763659/100000000:ℝ)) (u:=(38881871/50000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p173:(90987/100000:ℝ)≤Real.exp (-(1889/20000):ℝ)∧Real.exp (-(1889/20000):ℝ)≤(22747/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1889/20000):ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1889/20000):ℝ)) (l:=(909873/1000000:ℝ)) (u:=(454937/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p176:(93307/100000:ℝ)≤Real.exp (-(6927/100000):ℝ)∧Real.exp (-(6927/100000):ℝ)≤(23327/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(6927/100000):ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(6927/100000):ℝ)) (l:=(58317/62500:ℝ)) (u:=(37323/40000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p180:(6629/10000:ℝ)≤Real.exp (-(5139/12500):ℝ)∧Real.exp (-(5139/12500):ℝ)≤(66291/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(5139/12500):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(5139/12500):ℝ)) (l:=(662907/1000000:ℝ)) (u:=(662909/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p214:(22209/100000:ℝ)≤Real.exp (-(75233/50000):ℝ)∧Real.exp (-(75233/50000):ℝ)≤(2221/10000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(75233/200000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(75233/200000):ℝ)) (l:=(686489/1000000:ℝ)) (u:=(68649/100000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p216:(1947/2500:ℝ)≤Real.exp (-(1/4):ℝ)∧Real.exp (-(1/4):ℝ)≤(77881/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1/4):ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1/4):ℝ)) (l:=(1947/2500:ℝ)) (u:=(778801/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p219:(52937/100000:ℝ)≤Real.exp (-(12721/20000):ℝ)∧Real.exp (-(12721/20000):ℝ)≤(26469/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(12721/40000):ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(12721/40000):ℝ)) (l:=(727581/1000000:ℝ)) (u:=(145517/200000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p221:(927/25000:ℝ)≤Real.exp (-(164733/50000):ℝ)∧Real.exp (-(164733/50000):ℝ)≤(37081/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(164733/400000):ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(164733/400000):ℝ)) (l:=(132487/200000:ℝ)) (u:=(165609/250000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p222:(21861/100000:ℝ)≤Real.exp (-(30409/20000):ℝ)∧Real.exp (-(30409/20000):ℝ)≤(10931/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(30409/80000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(30409/80000):ℝ)) (l:=(85473/125000:ℝ)) (u:=(136757/200000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p224:(8979/12500:ℝ)≤Real.exp (-(8271/25000):ℝ)∧Real.exp (-(8271/25000):ℝ)≤(71833/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(8271/25000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(8271/25000):ℝ)) (l:=(8979/12500:ℝ)) (u:=(718321/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p227:(1/50000:ℝ)≤Real.exp (-(135247/12500):ℝ)∧Real.exp (-(135247/12500):ℝ)≤(20001/1000000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(135247/400000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(135247/400000):ℝ)) (l:=(71311147/100000000:ℝ)) (u:=(71311171/100000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p244:(16991/20000:ℝ)≤Real.exp (-(1019/6250):ℝ)∧Real.exp (-(1019/6250):ℝ)≤(21239/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1019/6250):ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1019/6250):ℝ)) (l:=(212389/250000:ℝ)) (u:=(21239/25000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p255:(58039/1000000:ℝ)≤Real.exp (-(35583/12500):ℝ)∧Real.exp (-(35583/12500):ℝ)≤(1451/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(35583/100000):ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(35583/100000):ℝ)) (l:=(70059171/100000000:ℝ)) (u:=(17514793/25000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p257:(3417/500000000:ℝ)≤Real.exp (-(14867/1250):ℝ)∧Real.exp (-(14867/1250):ℝ)≤(68341/10000000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(14867/40000):ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(14867/40000):ℝ)) (l:=(689578319/1000000000:ℝ)) (u:=(6895783199/10000000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p258:(60271/1000000000:ℝ)≤Real.exp (-(194333/20000):ℝ)∧Real.exp (-(194333/20000):ℝ)≤(3767/62500000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(194333/640000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(194333/640000):ℝ)) (l:=(73812261/100000000:ℝ)) (u:=(73812273/100000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p259:(8631/50000:ℝ)≤Real.exp (-(10979/6250):ℝ)∧Real.exp (-(10979/6250):ℝ)≤(17263/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(10979/25000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(10979/25000):ℝ)) (l:=(644577/1000000:ℝ)) (u:=(644579/1000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p260:(4711/2000000:ℝ)≤Real.exp (-(302549/50000):ℝ)∧Real.exp (-(302549/50000):ℝ)≤(5889/2500000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(302549/800000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(302549/800000):ℝ)) (l:=(17127571/25000000:ℝ)) (u:=(13702067/20000000:ℝ)) (n:=16)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p261:(2703/312500000:ℝ)≤Real.exp (-(1165799/100000):ℝ)∧Real.exp (-(1165799/100000):ℝ)≤(86497/10000000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1165799/3200000):ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1165799/3200000):ℝ)) (l:=(69467427/100000000:ℝ)) (u:=(6946743/10000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p262:(56239/1000000000:ℝ)≤Real.exp (-(97859/10000):ℝ)∧Real.exp (-(97859/10000):ℝ)≤(703/12500000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(97859/320000):ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(97859/320000):ℝ)) (l:=(1473054013/2000000000:ℝ)) (u:=(7365270067/10000000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p263:(443/20000000:ℝ)≤Real.exp (-(214353/20000):ℝ)∧Real.exp (-(214353/20000):ℝ)≤(22151/1000000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(214353/640000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(214353/640000):ℝ)) (l:=(3576953/5000000:ℝ)) (u:=(35769541/50000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p264:(6171/62500:ℝ)≤Real.exp (-(23153/10000):ℝ)∧Real.exp (-(23153/10000):ℝ)≤(98737/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(23153/80000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(23153/80000):ℝ)) (l:=(74870329/100000000:ℝ)) (u:=(37435169/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p265:(87079/100000:ℝ)≤Real.exp (-(2767/20000):ℝ)∧Real.exp (-(2767/20000):ℝ)≤(2177/2500:ℝ):=by
 have h:=Real.exp_bound (x:=(-(2767/20000):ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(2767/20000):ℝ)) (l:=(870793/1000000:ℝ)) (u:=(174159/200000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p266:(60907/10000000:ℝ)≤Real.exp (-(255049/50000):ℝ)∧Real.exp (-(255049/50000):ℝ)≤(15227/2500000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(255049/800000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(255049/800000):ℝ)) (l:=(36350637/50000000:ℝ)) (u:=(7270129/10000000:ℝ)) (n:=16)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p267:(449/31250:ℝ)≤Real.exp (-(16971/4000):ℝ)∧Real.exp (-(16971/4000):ℝ)≤(14369/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(16971/64000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(16971/64000):ℝ)) (l:=(76707409/100000000:ℝ)) (u:=(38353707/50000000:ℝ)) (n:=16)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p271:(34609/500000000:ℝ)≤Real.exp (-(29932/3125):ℝ)∧Real.exp (-(29932/3125):ℝ)≤(69219/1000000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(7483/25000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(7483/25000):ℝ)) (l:=(37066107/50000000:ℝ)) (u:=(289579/390625:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p272:(4699/25000000:ℝ)≤Real.exp (-(214481/25000):ℝ)∧Real.exp (-(214481/25000):ℝ)≤(18797/100000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(214481/800000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(214481/800000):ℝ)) (l:=(76483033/100000000:ℝ)) (u:=(38241519/50000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p273:(8869/5000000:ℝ)≤Real.exp (-(633459/100000):ℝ)∧Real.exp (-(633459/100000):ℝ)≤(17739/10000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(633459/1600000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(633459/1600000):ℝ)) (l:=(6730659497/10000000000:ℝ)) (u:=(1682666603/2500000000:ℝ)) (n:=16)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p275:(4801/25000:ℝ)≤Real.exp (-(33/20):ℝ)∧Real.exp (-(33/20):ℝ)≤(3841/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(33/80):ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(33/80):ℝ)) (l:=(13239863/20000000:ℝ)) (u:=(66199321/100000000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p276:(48759/100000:ℝ)≤Real.exp (-(17957/25000):ℝ)∧Real.exp (-(17957/25000):ℝ)≤(1219/2500:ℝ):=by
 have h:=Real.exp_bound (x:=(-(17957/50000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(17957/50000):ℝ)) (l:=(13965531/20000000:ℝ)) (u:=(69827691/100000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p278:(19251/100000:ℝ)≤Real.exp (-(4119/2500):ℝ)∧Real.exp (-(4119/2500):ℝ)≤(4813/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(4119/10000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(4119/10000):ℝ)) (l:=(66239/100000:ℝ)) (u:=(82799/125000:ℝ)) (n:=4)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p279:(58199/100000:ℝ)≤Real.exp (-(5413/10000):ℝ)∧Real.exp (-(5413/10000):ℝ)≤(291/500:ℝ):=by
 have h:=Real.exp_bound (x:=(-(5413/20000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(5413/20000):ℝ)) (l:=(762883/1000000:ℝ)) (u:=(190721/250000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p280:(16497/250000:ℝ)≤Real.exp (-(271827/100000):ℝ)∧Real.exp (-(271827/100000):ℝ)≤(65989/1000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(271827/800000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(271827/800000):ℝ)) (l:=(8899053/12500000:ℝ)) (u:=(556191/781250:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p285:(9197/25000:ℝ)≤Real.exp (-(999989199/1000000000):ℝ)∧Real.exp (-(999989199/1000000000):ℝ)≤(36789/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(999989199/2000000000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(999989199/2000000000):ℝ)) (l:=(606533/1000000:ℝ)) (u:=(303269/500000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p286:(38963/100000:ℝ)≤Real.exp (-(471269/500000):ℝ)∧Real.exp (-(471269/500000):ℝ)≤(9741/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(471269/1000000):ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(471269/1000000):ℝ)) (l:=(624209/1000000:ℝ)) (u:=(62421/100000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p315:(5399/500000000:ℝ)≤Real.exp (-(1143611/100000):ℝ)∧Real.exp (-(1143611/100000):ℝ)≤(10799/1000000000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(1143611/3200000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(1143611/3200000):ℝ)) (l:=(6995077/10000000:ℝ)) (u:=(17487701/25000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p318:(57457/1000000:ℝ)≤Real.exp (-(285671/100000):ℝ)∧Real.exp (-(285671/100000):ℝ)≤(28729/500000:ℝ):=by
 have h:=Real.exp_bound (x:=(-(285671/800000):ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(-(285671/800000):ℝ)) (l:=(69971/100000:ℝ)) (u:=(699711/1000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
end EmlComplexity.ExpBoundsProof_negative

theorem solution :
((6829/100000:ℝ)≤Real.exp (-(134199/50000):ℝ)∧Real.exp (-(134199/50000):ℝ)≤(68291/1000000:ℝ)) ∧
((999/1000:ℝ)≤Real.exp (-(1/1000):ℝ)∧Real.exp (-(1/1000):ℝ)≤(99901/100000:ℝ)) ∧
((30721/5000000000:ℝ)≤Real.exp (-12:ℝ)∧Real.exp (-12:ℝ)≤(61443/10000000000:ℝ)) ∧
((91/2500:ℝ)≤Real.exp (-(331317/100000):ℝ)∧Real.exp (-(331317/100000):ℝ)≤(36401/1000000:ℝ)) ∧
((19771/100000:ℝ)≤Real.exp (-(81047/50000):ℝ)∧Real.exp (-(81047/50000):ℝ)≤(4943/25000:ℝ)) ∧
((27067/50000:ℝ)≤Real.exp (-(61369/100000):ℝ)∧Real.exp (-(61369/100000):ℝ)≤(10827/20000:ℝ)) ∧
((47561/50000:ℝ)≤Real.exp (-(1/20):ℝ)∧Real.exp (-(1/20):ℝ)≤(95123/100000:ℝ)) ∧
((27/2500000:ℝ)≤Real.exp (-(571797/50000):ℝ)∧Real.exp (-(571797/50000):ℝ)≤(10801/1000000000:ℝ)) ∧
((57461/1000000:ℝ)≤Real.exp (-(8927/3125):ℝ)∧Real.exp (-(8927/3125):ℝ)≤(28731/500000:ℝ)) ∧
((34119/500000:ℝ)≤Real.exp (-(134237/50000):ℝ)∧Real.exp (-(134237/50000):ℝ)≤(68239/1000000:ℝ)) ∧
((5273/100000:ℝ)≤Real.exp (-(18391/6250):ℝ)∧Real.exp (-(18391/6250):ℝ)≤(52731/1000000:ℝ)) ∧
((2403/12500:ℝ)≤Real.exp (-(1649/1000):ℝ)∧Real.exp (-(1649/1000):ℝ)≤(769/4000:ℝ)) ∧
((12037/100000:ℝ)≤Real.exp (-(211717/100000):ℝ)∧Real.exp (-(211717/100000):ℝ)≤(6019/50000:ℝ)) ∧
((16543/25000:ℝ)≤Real.exp (-(41291/100000):ℝ)∧Real.exp (-(41291/100000):ℝ)≤(66173/100000:ℝ)) ∧
((19449/25000:ℝ)≤Real.exp (-(6277/25000):ℝ)∧Real.exp (-(6277/25000):ℝ)≤(77797/100000:ℝ)) ∧
((1/1000:ℝ)≤Real.exp (-(345387/50000):ℝ)∧Real.exp (-(345387/50000):ℝ)≤(10001/10000000:ℝ)) ∧
((24751/25000:ℝ)≤Real.exp (-(1/100):ℝ)∧Real.exp (-(1/100):ℝ)≤(19801/20000:ℝ)) ∧
((45869/100000:ℝ)≤Real.exp (-(77937/100000):ℝ)∧Real.exp (-(77937/100000):ℝ)≤(4587/10000:ℝ)) ∧
((1767/25000:ℝ)≤Real.exp (-(132479/50000):ℝ)∧Real.exp (-(132479/50000):ℝ)≤(70681/1000000:ℝ)) ∧
((90483/100000:ℝ)≤Real.exp (-(1/10):ℝ)∧Real.exp (-(1/10):ℝ)≤(22621/25000:ℝ)) ∧
((10811/1000000000:ℝ)≤Real.exp (-(571747/50000):ℝ)∧Real.exp (-(571747/50000):ℝ)≤(2703/250000000:ℝ)) ∧
((60407/1000000:ℝ)≤Real.exp (-(35083/12500):ℝ)∧Real.exp (-(35083/12500):ℝ)≤(7551/125000:ℝ)) ∧
((68271/10000000000:ℝ)≤Real.exp (-(59473/5000):ℝ)∧Real.exp (-(59473/5000):ℝ)≤(4267/625000000:ℝ)) ∧
((60211/1000000000:ℝ)≤Real.exp (-(194353/20000):ℝ)∧Real.exp (-(194353/20000):ℝ)≤(15053/250000000:ℝ)) ∧
((15619/100000:ℝ)≤Real.exp (-(5802/3125):ℝ)∧Real.exp (-(5802/3125):ℝ)≤(781/5000:ℝ)) ∧
((11203/5000000:ℝ)≤Real.exp (-(305049/50000):ℝ)∧Real.exp (-(305049/50000):ℝ)≤(22407/10000000:ℝ)) ∧
((69149/1000000000:ℝ)≤Real.exp (-(239481/25000):ℝ)∧Real.exp (-(239481/25000):ℝ)≤(1383/20000000:ℝ)) ∧
((17937/100000:ℝ)≤Real.exp (-(42957/25000):ℝ)∧Real.exp (-(42957/25000):ℝ)≤(8969/50000:ℝ)) ∧
((9197/25000:ℝ)≤Real.exp (-(99999/100000):ℝ)∧Real.exp (-(99999/100000):ℝ)≤(36789/100000:ℝ)) ∧
((92133/100000:ℝ)≤Real.exp (-(8193/100000):ℝ)∧Real.exp (-(8193/100000):ℝ)≤(46067/50000:ℝ)) ∧
((36349/1000000:ℝ)≤Real.exp (-(165729/50000):ℝ)∧Real.exp (-(165729/50000):ℝ)≤(727/20000:ℝ)) ∧
((3953/20000:ℝ)≤Real.exp (-(81061/50000):ℝ)∧Real.exp (-(81061/50000):ℝ)≤(9883/50000:ℝ)) ∧
((5413/10000:ℝ)≤Real.exp (-(30689/50000):ℝ)∧Real.exp (-(30689/50000):ℝ)≤(54131/100000:ℝ)) ∧
((179/4000:ℝ)≤Real.exp (-(62133/20000):ℝ)∧Real.exp (-(62133/20000):ℝ)≤(44751/1000000:ℝ)) ∧
((19479/100000:ℝ)≤Real.exp (-(81791/50000):ℝ)∧Real.exp (-(81791/50000):ℝ)≤(487/2500:ℝ)) ∧
((9097/50000:ℝ)≤Real.exp (-(85203/50000):ℝ)∧Real.exp (-(85203/50000):ℝ)≤(3639/20000:ℝ)) ∧
((10577/100000:ℝ)≤Real.exp (-(224647/100000):ℝ)∧Real.exp (-(224647/100000):ℝ)≤(5289/50000:ℝ)) ∧
((15511/100000:ℝ)≤Real.exp (-(186361/100000):ℝ)∧Real.exp (-(186361/100000):ℝ)≤(1939/12500:ℝ)) ∧
((45871/100000:ℝ)≤Real.exp (-(19483/25000):ℝ)∧Real.exp (-(19483/25000):ℝ)≤(2867/6250:ℝ)) ∧
((60471/100000:ℝ)≤Real.exp (-(50299/100000):ℝ)∧Real.exp (-(50299/100000):ℝ)≤(7559/12500:ℝ)) ∧
((90987/100000:ℝ)≤Real.exp (-(1889/20000):ℝ)∧Real.exp (-(1889/20000):ℝ)≤(22747/25000:ℝ)) ∧
((93307/100000:ℝ)≤Real.exp (-(6927/100000):ℝ)∧Real.exp (-(6927/100000):ℝ)≤(23327/25000:ℝ)) ∧
((6629/10000:ℝ)≤Real.exp (-(5139/12500):ℝ)∧Real.exp (-(5139/12500):ℝ)≤(66291/100000:ℝ)) ∧
((22209/100000:ℝ)≤Real.exp (-(75233/50000):ℝ)∧Real.exp (-(75233/50000):ℝ)≤(2221/10000:ℝ)) ∧
((1947/2500:ℝ)≤Real.exp (-(1/4):ℝ)∧Real.exp (-(1/4):ℝ)≤(77881/100000:ℝ)) ∧
((52937/100000:ℝ)≤Real.exp (-(12721/20000):ℝ)∧Real.exp (-(12721/20000):ℝ)≤(26469/50000:ℝ)) ∧
((927/25000:ℝ)≤Real.exp (-(164733/50000):ℝ)∧Real.exp (-(164733/50000):ℝ)≤(37081/1000000:ℝ)) ∧
((21861/100000:ℝ)≤Real.exp (-(30409/20000):ℝ)∧Real.exp (-(30409/20000):ℝ)≤(10931/50000:ℝ)) ∧
((8979/12500:ℝ)≤Real.exp (-(8271/25000):ℝ)∧Real.exp (-(8271/25000):ℝ)≤(71833/100000:ℝ)) ∧
((1/50000:ℝ)≤Real.exp (-(135247/12500):ℝ)∧Real.exp (-(135247/12500):ℝ)≤(20001/1000000000:ℝ)) ∧
((16991/20000:ℝ)≤Real.exp (-(1019/6250):ℝ)∧Real.exp (-(1019/6250):ℝ)≤(21239/25000:ℝ)) ∧
((58039/1000000:ℝ)≤Real.exp (-(35583/12500):ℝ)∧Real.exp (-(35583/12500):ℝ)≤(1451/25000:ℝ)) ∧
((3417/500000000:ℝ)≤Real.exp (-(14867/1250):ℝ)∧Real.exp (-(14867/1250):ℝ)≤(68341/10000000000:ℝ)) ∧
((60271/1000000000:ℝ)≤Real.exp (-(194333/20000):ℝ)∧Real.exp (-(194333/20000):ℝ)≤(3767/62500000:ℝ)) ∧
((8631/50000:ℝ)≤Real.exp (-(10979/6250):ℝ)∧Real.exp (-(10979/6250):ℝ)≤(17263/100000:ℝ)) ∧
((4711/2000000:ℝ)≤Real.exp (-(302549/50000):ℝ)∧Real.exp (-(302549/50000):ℝ)≤(5889/2500000:ℝ)) ∧
((2703/312500000:ℝ)≤Real.exp (-(1165799/100000):ℝ)∧Real.exp (-(1165799/100000):ℝ)≤(86497/10000000000:ℝ)) ∧
((56239/1000000000:ℝ)≤Real.exp (-(97859/10000):ℝ)∧Real.exp (-(97859/10000):ℝ)≤(703/12500000:ℝ)) ∧
((443/20000000:ℝ)≤Real.exp (-(214353/20000):ℝ)∧Real.exp (-(214353/20000):ℝ)≤(22151/1000000000:ℝ)) ∧
((6171/62500:ℝ)≤Real.exp (-(23153/10000):ℝ)∧Real.exp (-(23153/10000):ℝ)≤(98737/1000000:ℝ)) ∧
((87079/100000:ℝ)≤Real.exp (-(2767/20000):ℝ)∧Real.exp (-(2767/20000):ℝ)≤(2177/2500:ℝ)) ∧
((60907/10000000:ℝ)≤Real.exp (-(255049/50000):ℝ)∧Real.exp (-(255049/50000):ℝ)≤(15227/2500000:ℝ)) ∧
((449/31250:ℝ)≤Real.exp (-(16971/4000):ℝ)∧Real.exp (-(16971/4000):ℝ)≤(14369/1000000:ℝ)) ∧
((34609/500000000:ℝ)≤Real.exp (-(29932/3125):ℝ)∧Real.exp (-(29932/3125):ℝ)≤(69219/1000000000:ℝ)) ∧
((4699/25000000:ℝ)≤Real.exp (-(214481/25000):ℝ)∧Real.exp (-(214481/25000):ℝ)≤(18797/100000000:ℝ)) ∧
((8869/5000000:ℝ)≤Real.exp (-(633459/100000):ℝ)∧Real.exp (-(633459/100000):ℝ)≤(17739/10000000:ℝ)) ∧
((4801/25000:ℝ)≤Real.exp (-(33/20):ℝ)∧Real.exp (-(33/20):ℝ)≤(3841/20000:ℝ)) ∧
((48759/100000:ℝ)≤Real.exp (-(17957/25000):ℝ)∧Real.exp (-(17957/25000):ℝ)≤(1219/2500:ℝ)) ∧
((19251/100000:ℝ)≤Real.exp (-(4119/2500):ℝ)∧Real.exp (-(4119/2500):ℝ)≤(4813/25000:ℝ)) ∧
((58199/100000:ℝ)≤Real.exp (-(5413/10000):ℝ)∧Real.exp (-(5413/10000):ℝ)≤(291/500:ℝ)) ∧
((16497/250000:ℝ)≤Real.exp (-(271827/100000):ℝ)∧Real.exp (-(271827/100000):ℝ)≤(65989/1000000:ℝ)) ∧
((9197/25000:ℝ)≤Real.exp (-(999989199/1000000000):ℝ)∧Real.exp (-(999989199/1000000000):ℝ)≤(36789/100000:ℝ)) ∧
((38963/100000:ℝ)≤Real.exp (-(471269/500000):ℝ)∧Real.exp (-(471269/500000):ℝ)≤(9741/25000:ℝ)) ∧
((5399/500000000:ℝ)≤Real.exp (-(1143611/100000):ℝ)∧Real.exp (-(1143611/100000):ℝ)≤(10799/1000000000:ℝ)) ∧
((57457/1000000:ℝ)≤Real.exp (-(285671/100000):ℝ)∧Real.exp (-(285671/100000):ℝ)≤(28729/500000:ℝ)) := by
 exact ⟨EmlComplexity.ExpBoundsProof_negative.p12,⟨EmlComplexity.ExpBoundsProof_negative.p19,⟨EmlComplexity.ExpBoundsProof_negative.p22,⟨EmlComplexity.ExpBoundsProof_negative.p26,⟨EmlComplexity.ExpBoundsProof_negative.p28,⟨EmlComplexity.ExpBoundsProof_negative.p33,⟨EmlComplexity.ExpBoundsProof_negative.p41,⟨EmlComplexity.ExpBoundsProof_negative.p46,⟨EmlComplexity.ExpBoundsProof_negative.p47,⟨EmlComplexity.ExpBoundsProof_negative.p56,⟨EmlComplexity.ExpBoundsProof_negative.p62,⟨EmlComplexity.ExpBoundsProof_negative.p64,⟨EmlComplexity.ExpBoundsProof_negative.p66,⟨EmlComplexity.ExpBoundsProof_negative.p72,⟨EmlComplexity.ExpBoundsProof_negative.p75,⟨EmlComplexity.ExpBoundsProof_negative.p82,⟨EmlComplexity.ExpBoundsProof_negative.p89,⟨EmlComplexity.ExpBoundsProof_negative.p92,⟨EmlComplexity.ExpBoundsProof_negative.p94,⟨EmlComplexity.ExpBoundsProof_negative.p96,⟨EmlComplexity.ExpBoundsProof_negative.p107,⟨EmlComplexity.ExpBoundsProof_negative.p108,⟨EmlComplexity.ExpBoundsProof_negative.p109,⟨EmlComplexity.ExpBoundsProof_negative.p110,⟨EmlComplexity.ExpBoundsProof_negative.p111,⟨EmlComplexity.ExpBoundsProof_negative.p112,⟨EmlComplexity.ExpBoundsProof_negative.p114,⟨EmlComplexity.ExpBoundsProof_negative.p116,⟨EmlComplexity.ExpBoundsProof_negative.p118,⟨EmlComplexity.ExpBoundsProof_negative.p131,⟨EmlComplexity.ExpBoundsProof_negative.p132,⟨EmlComplexity.ExpBoundsProof_negative.p135,⟨EmlComplexity.ExpBoundsProof_negative.p141,⟨EmlComplexity.ExpBoundsProof_negative.p152,⟨EmlComplexity.ExpBoundsProof_negative.p154,⟨EmlComplexity.ExpBoundsProof_negative.p156,⟨EmlComplexity.ExpBoundsProof_negative.p158,⟨EmlComplexity.ExpBoundsProof_negative.p161,⟨EmlComplexity.ExpBoundsProof_negative.p163,⟨EmlComplexity.ExpBoundsProof_negative.p171,⟨EmlComplexity.ExpBoundsProof_negative.p173,⟨EmlComplexity.ExpBoundsProof_negative.p176,⟨EmlComplexity.ExpBoundsProof_negative.p180,⟨EmlComplexity.ExpBoundsProof_negative.p214,⟨EmlComplexity.ExpBoundsProof_negative.p216,⟨EmlComplexity.ExpBoundsProof_negative.p219,⟨EmlComplexity.ExpBoundsProof_negative.p221,⟨EmlComplexity.ExpBoundsProof_negative.p222,⟨EmlComplexity.ExpBoundsProof_negative.p224,⟨EmlComplexity.ExpBoundsProof_negative.p227,⟨EmlComplexity.ExpBoundsProof_negative.p244,⟨EmlComplexity.ExpBoundsProof_negative.p255,⟨EmlComplexity.ExpBoundsProof_negative.p257,⟨EmlComplexity.ExpBoundsProof_negative.p258,⟨EmlComplexity.ExpBoundsProof_negative.p259,⟨EmlComplexity.ExpBoundsProof_negative.p260,⟨EmlComplexity.ExpBoundsProof_negative.p261,⟨EmlComplexity.ExpBoundsProof_negative.p262,⟨EmlComplexity.ExpBoundsProof_negative.p263,⟨EmlComplexity.ExpBoundsProof_negative.p264,⟨EmlComplexity.ExpBoundsProof_negative.p265,⟨EmlComplexity.ExpBoundsProof_negative.p266,⟨EmlComplexity.ExpBoundsProof_negative.p267,⟨EmlComplexity.ExpBoundsProof_negative.p271,⟨EmlComplexity.ExpBoundsProof_negative.p272,⟨EmlComplexity.ExpBoundsProof_negative.p273,⟨EmlComplexity.ExpBoundsProof_negative.p275,⟨EmlComplexity.ExpBoundsProof_negative.p276,⟨EmlComplexity.ExpBoundsProof_negative.p278,⟨EmlComplexity.ExpBoundsProof_negative.p279,⟨EmlComplexity.ExpBoundsProof_negative.p280,⟨EmlComplexity.ExpBoundsProof_negative.p285,⟨EmlComplexity.ExpBoundsProof_negative.p286,⟨EmlComplexity.ExpBoundsProof_negative.p315,EmlComplexity.ExpBoundsProof_negative.p318⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms solution
