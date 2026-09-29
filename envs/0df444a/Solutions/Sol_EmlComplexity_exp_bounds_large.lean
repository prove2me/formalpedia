-- Prove2me | solution 1 for EmlComplexity.exp_bounds_large
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T08:07:20.290992+00:00
-- url     : https://prove2.me/submissions/4868081b-33a0-4ee3-8116-e971adfbffa2

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace EmlComplexity.ExpBoundsProof_large
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
lemma p1:(1515423/100000:ℝ)≤Real.exp (67957/25000:ℝ)∧Real.exp (67957/25000:ℝ)≤(47357/3125:ℝ):=by
 have h:=Real.exp_bound (x:=(67957/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(67957/200000:ℝ)) (l:=(70232277/50000000:ℝ)) (u:=(35116139/25000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p4:(2202646579/100000:ℝ)≤Real.exp (10:ℝ)∧Real.exp (10:ℝ)≤(110132329/5000:ℝ):=by
 have h:=Real.exp_bound (x:=(5/16:ℝ)) (by norm_num) (n:=10) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(5/16:ℝ)) (l:=(85427371323/62500000000:ℝ)) (u:=(683418970587/500000000000:ℝ)) (n:=32)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p6:(1415403/100000:ℝ)≤Real.exp (53/20:ℝ)∧Real.exp (53/20:ℝ)≤(353851/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(53/160:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(53/160:ℝ)) (l:=(139270791/100000000:ℝ)) (u:=(139270793/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p7:(881927/100000:ℝ)≤Real.exp (108847/50000:ℝ)∧Real.exp (108847/50000:ℝ)≤(110241/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(108847/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(108847/400000:ℝ)) (l:=(131274119/100000000:ℝ)) (u:=(1050193/800000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p8:(2968263/20000:ℝ)≤Real.exp (5:ℝ)∧Real.exp (5:ℝ)≤(3710329/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(5/16:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(5/16:ℝ)) (l:=(6834189681/5000000000:ℝ)) (u:=(6834189707/5000000000:ℝ)) (n:=16)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p13:(757719/50000:ℝ)≤Real.exp (271829/100000:ℝ)∧Real.exp (271829/100000:ℝ)≤(1515439/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(271829/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(271829/800000:ℝ)) (l:=(14046473/10000000:ℝ)) (u:=(35116183/25000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p14:(70773/5000:ℝ)≤Real.exp (66251/25000:ℝ)∧Real.exp (66251/25000:ℝ)≤(1415461/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(66251/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(66251/200000:ℝ)) (l:=(2176117/1562500:ℝ)) (u:=(139271489/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p15:(365317/25000:ℝ)≤Real.exp (268189/100000:ℝ)∧Real.exp (268189/100000:ℝ)≤(1461269/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(268189/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(268189/800000:ℝ)) (l:=(139827067/100000000:ℝ)) (u:=(139827069/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p16:(62179/5000:ℝ)≤Real.exp (126029/50000:ℝ)∧Real.exp (126029/50000:ℝ)≤(1243581/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(126029/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(126029/400000:ℝ)) (l:=(27407173/20000000:ℝ)) (u:=(68517933/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p23:(2008553/100000:ℝ)≤Real.exp (3:ℝ)∧Real.exp (3:ℝ)≤(1004277/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(3/8:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(3/8:ℝ)) (l:=(145499139/100000000:ℝ)) (u:=(72749571/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p27:(730663/50000:ℝ)≤Real.exp (268193/100000:ℝ)∧Real.exp (268193/100000:ℝ)≤(1461327/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(268193/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(268193/800000:ℝ)) (l:=(139827767/100000000:ℝ)) (u:=(17478471/12500000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p29:(124363/10000:ℝ)≤Real.exp (126031/50000:ℝ)∧Real.exp (126031/50000:ℝ)≤(1243631/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(126031/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(126031/400000:ℝ)) (l:=(2740731/2000000:ℝ)) (u:=(17129569/12500000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p34:(1437599/100000:ℝ)≤Real.exp (66639/25000:ℝ)∧Real.exp (66639/25000:ℝ)≤(1797/125:ℝ):=by
 have h:=Real.exp_bound (x:=(66639/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(66639/200000:ℝ)) (l:=(139541937/100000000:ℝ)) (u:=(69770969/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p35:(1250401/100000:ℝ)≤Real.exp (50521/20000:ℝ)∧Real.exp (50521/20000:ℝ)≤(625201/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(50521/160000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(50521/160000:ℝ)) (l:=(27425919/20000000:ℝ)) (u:=(137129597/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p36:(167947/12500:ℝ)≤Real.exp (16237/6250:ℝ)∧Real.exp (16237/6250:ℝ)≤(1343577/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(16237/50000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(16237/50000:ℝ)) (l:=(138367083/100000000:ℝ)) (u:=(27673417/20000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p39:(390959/50000:ℝ)≤Real.exp (102829/50000:ℝ)∧Real.exp (102829/50000:ℝ)≤(781919/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(102829/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(102829/400000:ℝ)) (l:=(32328471/25000000:ℝ)) (u:=(4041059/3125000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p42:(39049/5000:ℝ)≤Real.exp (102769/50000:ℝ)∧Real.exp (102769/50000:ℝ)≤(780981/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(102769/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(102769/400000:ℝ)) (l:=(16161811/12500000:ℝ)) (u:=(129294493/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p48:(348059/20000:ℝ)≤Real.exp (8927/3125:ℝ)∧Real.exp (8927/3125:ℝ)≤(217537/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(8927/25000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(8927/25000:ℝ)) (l:=(71457509/50000000:ℝ)) (u:=(7145751/5000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p63:(1437671/100000:ℝ)≤Real.exp (266561/100000:ℝ)∧Real.exp (266561/100000:ℝ)≤(179709/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(266561/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(266561/800000:ℝ)) (l:=(139542809/100000000:ℝ)) (u:=(139542811/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p65:(1250451/100000:ℝ)≤Real.exp (252609/100000:ℝ)∧Real.exp (252609/100000:ℝ)≤(312613/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(252609/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(252609/800000:ℝ)) (l:=(137130281/100000000:ℝ)) (u:=(68565141/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p67:(134363/10000:ℝ)≤Real.exp (64949/25000:ℝ)∧Real.exp (64949/25000:ℝ)≤(1343631/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(64949/200000:ℝ)) (by norm_num) (n:=10) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(64949/200000:ℝ)) (l:=(13836777631/10000000000:ℝ)) (u:=(432399301/312500000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p73:(881963/100000:ℝ)≤Real.exp (108849/50000:ℝ)∧Real.exp (108849/50000:ℝ)≤(220491/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(108849/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(108849/400000:ℝ)) (l:=(6563739/5000000:ℝ)) (u:=(131274781/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p74:(195493/25000:ℝ)≤Real.exp (41133/20000:ℝ)∧Real.exp (41133/20000:ℝ)≤(781973/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(41133/160000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(41133/160000:ℝ)) (l:=(12931501589/10000000000:ℝ)) (u:=(6465750963/5000000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p77:(1449117/100000:ℝ)≤Real.exp (133677/50000:ℝ)∧Real.exp (133677/50000:ℝ)≤(724559/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(133677/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(133677/400000:ℝ)) (l:=(139681199/100000000:ℝ)) (u:=(139681201/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p78:(891899/50000:ℝ)≤Real.exp (288133/100000:ℝ)∧Real.exp (288133/100000:ℝ)≤(1783799/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(288133/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(288133/800000:ℝ)) (l:=(143356771/100000000:ℝ)) (u:=(143356773/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p79:(1247217/100000:ℝ)≤Real.exp (5047/2000:ℝ)∧Real.exp (5047/2000:ℝ)≤(623609/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(5047/16000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(5047/16000:ℝ)) (l:=(34271473/25000000:ℝ)) (u:=(68542947/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p80:(1263347/100000:ℝ)≤Real.exp (50727/20000:ℝ)∧Real.exp (50727/20000:ℝ)≤(315837/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(50727/160000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(50727/160000:ℝ)) (l:=(137306263/100000000:ℝ)) (u:=(27461253/20000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p81:(170417/12500:ℝ)≤Real.exp (65313/25000:ℝ)∧Real.exp (65313/25000:ℝ)≤(1363337/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(65313/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(65313/200000:ℝ)) (l:=(69309917/50000000:ℝ)) (u:=(34654959/25000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p83:(1297701/100000:ℝ)≤Real.exp (128159/50000:ℝ)∧Real.exp (128159/50000:ℝ)≤(648851/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(128159/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(128159/400000:ℝ)) (l:=(137767527/100000000:ℝ)) (u:=(137767529/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p84:(478953/50000:ℝ)≤Real.exp (112979/50000:ℝ)∧Real.exp (112979/50000:ℝ)≤(957907/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(112979/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(112979/400000:ℝ)) (l:=(132637207/100000000:ℝ)) (u:=(26527443/20000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p90:(413891/50000:ℝ)≤Real.exp (105679/50000:ℝ)∧Real.exp (105679/50000:ℝ)≤(827783/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(105679/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(105679/400000:ℝ)) (l:=(26047707/20000000:ℝ)) (u:=(6511927/5000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p100:(1265243/100000:ℝ)≤Real.exp (50757/20000:ℝ)∧Real.exp (50757/20000:ℝ)≤(316311/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(50757/160000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(50757/160000:ℝ)) (l:=(13733201/10000000:ℝ)) (u:=(34333003/25000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p113:(1863217/100000:ℝ)≤Real.exp (292489/100000:ℝ)∧Real.exp (292489/100000:ℝ)≤(931609/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(292489/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(292489/800000:ℝ)) (l:=(144139477/100000000:ℝ)) (u:=(3603487/2500000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p126:(1848907/100000:ℝ)≤Real.exp (145859/50000:ℝ)∧Real.exp (145859/50000:ℝ)≤(462227/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(145859/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(145859/400000:ℝ)) (l:=(144000629/100000000:ℝ)) (u:=(18000079/12500000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p153:(57967/4000:ℝ)≤Real.exp (133679/50000:ℝ)∧Real.exp (133679/50000:ℝ)≤(181147/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(133679/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(133679/400000:ℝ)) (l:=(139681897/100000000:ℝ)) (u:=(139681899/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p155:(1247267/100000:ℝ)≤Real.exp (126177/50000:ℝ)∧Real.exp (126177/50000:ℝ)≤(311817/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(126177/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(126177/400000:ℝ)) (l:=(137086577/100000000:ℝ)) (u:=(137086579/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p157:(1263397/100000:ℝ)≤Real.exp (253639/100000:ℝ)∧Real.exp (253639/100000:ℝ)≤(631699/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(253639/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(253639/800000:ℝ)) (l:=(13730695019/10000000000:ℝ)) (u:=(13730695077/10000000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p159:(340851/25000:ℝ)≤Real.exp (261257/100000:ℝ)∧Real.exp (261257/100000:ℝ)≤(272681/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(261257/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(261257/800000:ℝ)) (l:=(1386207/1000000:ℝ)) (u:=(69310351/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p160:(481291/50000:ℝ)≤Real.exp (45289/20000:ℝ)∧Real.exp (45289/20000:ℝ)≤(962583/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(45289/160000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(45289/160000:ℝ)) (l:=(5308719/4000000:ℝ)) (u:=(66358991/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p162:(648883/50000:ℝ)≤Real.exp (256323/100000:ℝ)∧Real.exp (256323/100000:ℝ)≤(1297767/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(256323/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(256323/800000:ℝ)) (l:=(34442097/25000000:ℝ)) (u:=(13776839/10000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p164:(957963/100000:ℝ)≤Real.exp (56491/25000:ℝ)∧Real.exp (56491/25000:ℝ)≤(239491/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(56491/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(56491/200000:ℝ)) (l:=(13263820843/10000000000:ℝ)) (u:=(13263820867/10000000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p172:(103481/12500:ℝ)≤Real.exp (105683/50000:ℝ)∧Real.exp (105683/50000:ℝ)≤(827849/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(105683/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(105683/400000:ℝ)) (l:=(130239837/100000000:ℝ)) (u:=(65119921/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p184:(757651/50000:ℝ)≤Real.exp (13591/5000:ℝ)∧Real.exp (13591/5000:ℝ)≤(1515303/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(13591/40000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(13591/40000:ℝ)) (l:=(2809263/2000000:ℝ)) (u:=(8778947/6250000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p187:(1443347/100000:ℝ)≤Real.exp (53391/20000:ℝ)∧Real.exp (53391/20000:ℝ)≤(360837/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(53391/160000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(53391/160000:ℝ)) (l:=(2792231/2000000:ℝ)) (u:=(4362861/3125000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p188:(134671/10000:ℝ)≤Real.exp (10401/4000:ℝ)∧Real.exp (10401/4000:ℝ)≤(1346711/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(10401/32000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(10401/32000:ℝ)) (l:=(138407389/100000000:ℝ)) (u:=(13840739/10000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p189:(461677/25000:ℝ)≤Real.exp (291599/100000:ℝ)∧Real.exp (291599/100000:ℝ)≤(1846709/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(291599/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(291599/800000:ℝ)) (l:=(143979211/100000000:ℝ)) (u:=(71989607/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p190:(1677483/100000:ℝ)≤Real.exp (70497/25000:ℝ)∧Real.exp (70497/25000:ℝ)≤(419371/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(70497/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(70497/200000:ℝ)) (l:=(14225983/10000000:ℝ)) (u:=(17782479/12500000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p191:(748681/50000:ℝ)≤Real.exp (270629/100000:ℝ)∧Real.exp (270629/100000:ℝ)≤(1497363/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(270629/800000:ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(270629/800000:ℝ)) (l:=(438294351/312500000:ℝ)) (u:=(3506354809/2500000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p192:(394191/25000:ℝ)≤Real.exp (68949/25000:ℝ)∧Real.exp (68949/25000:ℝ)≤(315353/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(68949/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(68949/200000:ℝ)) (l:=(141162989/100000000:ℝ)) (u:=(141162991/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p193:(1248839/100000:ℝ)≤Real.exp (1578/625:ℝ)∧Real.exp (1578/625:ℝ)≤(31221/2500:ℝ):=by
 have h:=Real.exp_bound (x:=(789/2500:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(789/2500:ℝ)) (l:=(13710817/10000000:ℝ)) (u:=(34277043/25000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p194:(1262791/100000:ℝ)≤Real.exp (253591/100000:ℝ)∧Real.exp (253591/100000:ℝ)≤(157849/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(253591/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(253591/800000:ℝ)) (l:=(17162339/12500000:ℝ)) (u:=(137298713/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p195:(627807/50000:ℝ)≤Real.exp (253021/100000:ℝ)∧Real.exp (253021/100000:ℝ)≤(251123/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(253021/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(253021/800000:ℝ)) (l:=(137200921/100000000:ℝ)) (u:=(137200923/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p196:(270757/20000:ℝ)≤Real.exp (260549/100000:ℝ)∧Real.exp (260549/100000:ℝ)≤(676893/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(260549/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(260549/800000:ℝ)) (l:=(5539923/4000000:ℝ)) (u:=(138498077/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p197:(141043/10000:ℝ)≤Real.exp (33081/12500:ℝ)∧Real.exp (33081/12500:ℝ)≤(1410431/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(33081/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(33081/100000:ℝ)) (l:=(69604763/50000000:ℝ)) (u:=(139209527/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p198:(261947/20000:ℝ)≤Real.exp (257241/100000:ℝ)∧Real.exp (257241/100000:ℝ)≤(163717/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(257241/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(257241/800000:ℝ)) (l:=(17240821/12500000:ℝ)) (u:=(13792657/10000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p200:(330341/25000:ℝ)≤Real.exp (413/160:ℝ)∧Real.exp (413/160:ℝ)≤(264273/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(413/1280:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(413/1280:ℝ)) (l:=(138079061/100000000:ℝ)) (u:=(138079063/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p201:(754287/50000:ℝ)≤Real.exp (2171/800:ℝ)∧Real.exp (2171/800:ℝ)≤(60343/4000:ℝ):=by
 have h:=Real.exp_bound (x:=(2171/6400:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(2171/6400:ℝ)) (l:=(1754812993/1250000000:ℝ)) (u:=(14038504043/10000000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p202:(2758963/100000:ℝ)≤Real.exp (10367/3125:ℝ)∧Real.exp (10367/3125:ℝ)≤(689741/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(10367/25000:ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(10367/25000:ℝ)) (l:=(7569431087/5000000000:ℝ)) (u:=(15138862197/10000000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p203:(1057909/100000:ℝ)≤Real.exp (14743/6250:ℝ)∧Real.exp (14743/6250:ℝ)≤(105791/10000:ℝ):=by
 have h:=Real.exp_bound (x:=(14743/50000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(14743/50000:ℝ)) (l:=(5371753/4000000:ℝ)) (u:=(67146917/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p206:(20647/2500:ℝ)≤Real.exp (26391/12500:ℝ)∧Real.exp (26391/12500:ℝ)≤(825881/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(26391/100000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(26391/100000:ℝ)) (l:=(130201097/100000000:ℝ)) (u:=(65100551/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p211:(804121/100000:ℝ)≤Real.exp (104229/50000:ℝ)∧Real.exp (104229/50000:ℝ)≤(402061/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(104229/400000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(104229/400000:ℝ)) (l:=(5190691/4000000:ℝ)) (u:=(1622091/1250000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p225:(410069/25000:ℝ)≤Real.exp (55949/20000:ℝ)∧Real.exp (55949/20000:ℝ)≤(1640277/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(55949/160000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(55949/160000:ℝ)) (l:=(17732691/12500000:ℝ)) (u:=(14186153/10000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p228:(89197/5000:ℝ)≤Real.exp (288141/100000:ℝ)∧Real.exp (288141/100000:ℝ)≤(1783941/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(288141/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(288141/800000:ℝ)) (l:=(35839551/25000000:ℝ)) (u:=(143358207/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p233:(18963/2500:ℝ)≤Real.exp (10131/5000:ℝ)∧Real.exp (10131/5000:ℝ)≤(758521/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(10131/40000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(10131/40000:ℝ)) (l:=(64411873/50000000:ℝ)) (u:=(103059/80000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p234:(91821/6250:ℝ)≤Real.exp (134363/50000:ℝ)∧Real.exp (134363/50000:ℝ)≤(1469137/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(134363/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(134363/400000:ℝ)) (l:=(69960479/50000000:ℝ)) (u:=(437253/312500:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p239:(1374919/100000:ℝ)≤Real.exp (131049/50000:ℝ)∧Real.exp (131049/50000:ℝ)≤(34373/2500:ℝ):=by
 have h:=Real.exp_bound (x:=(131049/400000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(131049/400000:ℝ)) (l:=(69383251/50000000:ℝ)) (u:=(17345813/12500000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p240:(18163/2000:ℝ)≤Real.exp (13789/6250:ℝ)∧Real.exp (13789/6250:ℝ)≤(908151/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(13789/50000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(13789/50000:ℝ)) (l:=(131755791/100000000:ℝ)) (u:=(65877899/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p241:(243493/12500:ℝ)≤Real.exp (37117/12500:ℝ)∧Real.exp (37117/12500:ℝ)≤(389589/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(37117/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(37117/100000:ℝ)) (l:=(144942943/100000000:ℝ)) (u:=(72471473/50000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p269:(94713/6250:ℝ)≤Real.exp (271827/100000:ℝ)∧Real.exp (271827/100000:ℝ)≤(1515409/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(271827/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(271827/800000:ℝ)) (l:=(140464379/100000000:ℝ)) (u:=(140464381/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p270:(1804737/100000:ℝ)≤Real.exp (2893/1000:ℝ)∧Real.exp (2893/1000:ℝ)≤(902369/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(2893/8000:ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(2893/8000:ℝ)) (l:=(14356604677/10000000000:ℝ)) (u:=(3589151171/2500000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p283:(252453/25000:ℝ)≤Real.exp (46247/20000:ℝ)∧Real.exp (46247/20000:ℝ)≤(1009813/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(46247/160000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(46247/160000:ℝ)) (l:=(66757503/50000000:ℝ)) (u:=(26703003/20000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p289:(1652261/100000:ℝ)≤Real.exp (280473/100000:ℝ)∧Real.exp (280473/100000:ℝ)≤(826131/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(280473/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(280473/800000:ℝ)) (l:=(3549767/2500000:ℝ)) (u:=(141990683/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p300:(881901/100000:ℝ)≤Real.exp (217691/100000:ℝ)∧Real.exp (217691/100000:ℝ)≤(440951/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(217691/800000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(217691/800000:ℝ)) (l:=(65636813/50000000:ℝ)) (u:=(4102301/3125000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p312:(1678977/100000:ℝ)≤Real.exp (282077/100000:ℝ)∧Real.exp (282077/100000:ℝ)≤(839489/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(282077/800000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(282077/800000:ℝ)) (l:=(142275657/100000000:ℝ)) (u:=(142275659/100000000:ℝ)) (n:=8)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
end EmlComplexity.ExpBoundsProof_large

theorem solution :
((1515423/100000:ℝ)≤Real.exp (67957/25000:ℝ)∧Real.exp (67957/25000:ℝ)≤(47357/3125:ℝ)) ∧
((2202646579/100000:ℝ)≤Real.exp (10:ℝ)∧Real.exp (10:ℝ)≤(110132329/5000:ℝ)) ∧
((1415403/100000:ℝ)≤Real.exp (53/20:ℝ)∧Real.exp (53/20:ℝ)≤(353851/25000:ℝ)) ∧
((881927/100000:ℝ)≤Real.exp (108847/50000:ℝ)∧Real.exp (108847/50000:ℝ)≤(110241/12500:ℝ)) ∧
((2968263/20000:ℝ)≤Real.exp (5:ℝ)∧Real.exp (5:ℝ)≤(3710329/25000:ℝ)) ∧
((757719/50000:ℝ)≤Real.exp (271829/100000:ℝ)∧Real.exp (271829/100000:ℝ)≤(1515439/100000:ℝ)) ∧
((70773/5000:ℝ)≤Real.exp (66251/25000:ℝ)∧Real.exp (66251/25000:ℝ)≤(1415461/100000:ℝ)) ∧
((365317/25000:ℝ)≤Real.exp (268189/100000:ℝ)∧Real.exp (268189/100000:ℝ)≤(1461269/100000:ℝ)) ∧
((62179/5000:ℝ)≤Real.exp (126029/50000:ℝ)∧Real.exp (126029/50000:ℝ)≤(1243581/100000:ℝ)) ∧
((2008553/100000:ℝ)≤Real.exp (3:ℝ)∧Real.exp (3:ℝ)≤(1004277/50000:ℝ)) ∧
((730663/50000:ℝ)≤Real.exp (268193/100000:ℝ)∧Real.exp (268193/100000:ℝ)≤(1461327/100000:ℝ)) ∧
((124363/10000:ℝ)≤Real.exp (126031/50000:ℝ)∧Real.exp (126031/50000:ℝ)≤(1243631/100000:ℝ)) ∧
((1437599/100000:ℝ)≤Real.exp (66639/25000:ℝ)∧Real.exp (66639/25000:ℝ)≤(1797/125:ℝ)) ∧
((1250401/100000:ℝ)≤Real.exp (50521/20000:ℝ)∧Real.exp (50521/20000:ℝ)≤(625201/50000:ℝ)) ∧
((167947/12500:ℝ)≤Real.exp (16237/6250:ℝ)∧Real.exp (16237/6250:ℝ)≤(1343577/100000:ℝ)) ∧
((390959/50000:ℝ)≤Real.exp (102829/50000:ℝ)∧Real.exp (102829/50000:ℝ)≤(781919/100000:ℝ)) ∧
((39049/5000:ℝ)≤Real.exp (102769/50000:ℝ)∧Real.exp (102769/50000:ℝ)≤(780981/100000:ℝ)) ∧
((348059/20000:ℝ)≤Real.exp (8927/3125:ℝ)∧Real.exp (8927/3125:ℝ)≤(217537/12500:ℝ)) ∧
((1437671/100000:ℝ)≤Real.exp (266561/100000:ℝ)∧Real.exp (266561/100000:ℝ)≤(179709/12500:ℝ)) ∧
((1250451/100000:ℝ)≤Real.exp (252609/100000:ℝ)∧Real.exp (252609/100000:ℝ)≤(312613/25000:ℝ)) ∧
((134363/10000:ℝ)≤Real.exp (64949/25000:ℝ)∧Real.exp (64949/25000:ℝ)≤(1343631/100000:ℝ)) ∧
((881963/100000:ℝ)≤Real.exp (108849/50000:ℝ)∧Real.exp (108849/50000:ℝ)≤(220491/25000:ℝ)) ∧
((195493/25000:ℝ)≤Real.exp (41133/20000:ℝ)∧Real.exp (41133/20000:ℝ)≤(781973/100000:ℝ)) ∧
((1449117/100000:ℝ)≤Real.exp (133677/50000:ℝ)∧Real.exp (133677/50000:ℝ)≤(724559/50000:ℝ)) ∧
((891899/50000:ℝ)≤Real.exp (288133/100000:ℝ)∧Real.exp (288133/100000:ℝ)≤(1783799/100000:ℝ)) ∧
((1247217/100000:ℝ)≤Real.exp (5047/2000:ℝ)∧Real.exp (5047/2000:ℝ)≤(623609/50000:ℝ)) ∧
((1263347/100000:ℝ)≤Real.exp (50727/20000:ℝ)∧Real.exp (50727/20000:ℝ)≤(315837/25000:ℝ)) ∧
((170417/12500:ℝ)≤Real.exp (65313/25000:ℝ)∧Real.exp (65313/25000:ℝ)≤(1363337/100000:ℝ)) ∧
((1297701/100000:ℝ)≤Real.exp (128159/50000:ℝ)∧Real.exp (128159/50000:ℝ)≤(648851/50000:ℝ)) ∧
((478953/50000:ℝ)≤Real.exp (112979/50000:ℝ)∧Real.exp (112979/50000:ℝ)≤(957907/100000:ℝ)) ∧
((413891/50000:ℝ)≤Real.exp (105679/50000:ℝ)∧Real.exp (105679/50000:ℝ)≤(827783/100000:ℝ)) ∧
((1265243/100000:ℝ)≤Real.exp (50757/20000:ℝ)∧Real.exp (50757/20000:ℝ)≤(316311/25000:ℝ)) ∧
((1863217/100000:ℝ)≤Real.exp (292489/100000:ℝ)∧Real.exp (292489/100000:ℝ)≤(931609/50000:ℝ)) ∧
((1848907/100000:ℝ)≤Real.exp (145859/50000:ℝ)∧Real.exp (145859/50000:ℝ)≤(462227/25000:ℝ)) ∧
((57967/4000:ℝ)≤Real.exp (133679/50000:ℝ)∧Real.exp (133679/50000:ℝ)≤(181147/12500:ℝ)) ∧
((1247267/100000:ℝ)≤Real.exp (126177/50000:ℝ)∧Real.exp (126177/50000:ℝ)≤(311817/25000:ℝ)) ∧
((1263397/100000:ℝ)≤Real.exp (253639/100000:ℝ)∧Real.exp (253639/100000:ℝ)≤(631699/50000:ℝ)) ∧
((340851/25000:ℝ)≤Real.exp (261257/100000:ℝ)∧Real.exp (261257/100000:ℝ)≤(272681/20000:ℝ)) ∧
((481291/50000:ℝ)≤Real.exp (45289/20000:ℝ)∧Real.exp (45289/20000:ℝ)≤(962583/100000:ℝ)) ∧
((648883/50000:ℝ)≤Real.exp (256323/100000:ℝ)∧Real.exp (256323/100000:ℝ)≤(1297767/100000:ℝ)) ∧
((957963/100000:ℝ)≤Real.exp (56491/25000:ℝ)∧Real.exp (56491/25000:ℝ)≤(239491/25000:ℝ)) ∧
((103481/12500:ℝ)≤Real.exp (105683/50000:ℝ)∧Real.exp (105683/50000:ℝ)≤(827849/100000:ℝ)) ∧
((757651/50000:ℝ)≤Real.exp (13591/5000:ℝ)∧Real.exp (13591/5000:ℝ)≤(1515303/100000:ℝ)) ∧
((1443347/100000:ℝ)≤Real.exp (53391/20000:ℝ)∧Real.exp (53391/20000:ℝ)≤(360837/25000:ℝ)) ∧
((134671/10000:ℝ)≤Real.exp (10401/4000:ℝ)∧Real.exp (10401/4000:ℝ)≤(1346711/100000:ℝ)) ∧
((461677/25000:ℝ)≤Real.exp (291599/100000:ℝ)∧Real.exp (291599/100000:ℝ)≤(1846709/100000:ℝ)) ∧
((1677483/100000:ℝ)≤Real.exp (70497/25000:ℝ)∧Real.exp (70497/25000:ℝ)≤(419371/25000:ℝ)) ∧
((748681/50000:ℝ)≤Real.exp (270629/100000:ℝ)∧Real.exp (270629/100000:ℝ)≤(1497363/100000:ℝ)) ∧
((394191/25000:ℝ)≤Real.exp (68949/25000:ℝ)∧Real.exp (68949/25000:ℝ)≤(315353/20000:ℝ)) ∧
((1248839/100000:ℝ)≤Real.exp (1578/625:ℝ)∧Real.exp (1578/625:ℝ)≤(31221/2500:ℝ)) ∧
((1262791/100000:ℝ)≤Real.exp (253591/100000:ℝ)∧Real.exp (253591/100000:ℝ)≤(157849/12500:ℝ)) ∧
((627807/50000:ℝ)≤Real.exp (253021/100000:ℝ)∧Real.exp (253021/100000:ℝ)≤(251123/20000:ℝ)) ∧
((270757/20000:ℝ)≤Real.exp (260549/100000:ℝ)∧Real.exp (260549/100000:ℝ)≤(676893/50000:ℝ)) ∧
((141043/10000:ℝ)≤Real.exp (33081/12500:ℝ)∧Real.exp (33081/12500:ℝ)≤(1410431/100000:ℝ)) ∧
((261947/20000:ℝ)≤Real.exp (257241/100000:ℝ)∧Real.exp (257241/100000:ℝ)≤(163717/12500:ℝ)) ∧
((330341/25000:ℝ)≤Real.exp (413/160:ℝ)∧Real.exp (413/160:ℝ)≤(264273/20000:ℝ)) ∧
((754287/50000:ℝ)≤Real.exp (2171/800:ℝ)∧Real.exp (2171/800:ℝ)≤(60343/4000:ℝ)) ∧
((2758963/100000:ℝ)≤Real.exp (10367/3125:ℝ)∧Real.exp (10367/3125:ℝ)≤(689741/25000:ℝ)) ∧
((1057909/100000:ℝ)≤Real.exp (14743/6250:ℝ)∧Real.exp (14743/6250:ℝ)≤(105791/10000:ℝ)) ∧
((20647/2500:ℝ)≤Real.exp (26391/12500:ℝ)∧Real.exp (26391/12500:ℝ)≤(825881/100000:ℝ)) ∧
((804121/100000:ℝ)≤Real.exp (104229/50000:ℝ)∧Real.exp (104229/50000:ℝ)≤(402061/50000:ℝ)) ∧
((410069/25000:ℝ)≤Real.exp (55949/20000:ℝ)∧Real.exp (55949/20000:ℝ)≤(1640277/100000:ℝ)) ∧
((89197/5000:ℝ)≤Real.exp (288141/100000:ℝ)∧Real.exp (288141/100000:ℝ)≤(1783941/100000:ℝ)) ∧
((18963/2500:ℝ)≤Real.exp (10131/5000:ℝ)∧Real.exp (10131/5000:ℝ)≤(758521/100000:ℝ)) ∧
((91821/6250:ℝ)≤Real.exp (134363/50000:ℝ)∧Real.exp (134363/50000:ℝ)≤(1469137/100000:ℝ)) ∧
((1374919/100000:ℝ)≤Real.exp (131049/50000:ℝ)∧Real.exp (131049/50000:ℝ)≤(34373/2500:ℝ)) ∧
((18163/2000:ℝ)≤Real.exp (13789/6250:ℝ)∧Real.exp (13789/6250:ℝ)≤(908151/100000:ℝ)) ∧
((243493/12500:ℝ)≤Real.exp (37117/12500:ℝ)∧Real.exp (37117/12500:ℝ)≤(389589/20000:ℝ)) ∧
((94713/6250:ℝ)≤Real.exp (271827/100000:ℝ)∧Real.exp (271827/100000:ℝ)≤(1515409/100000:ℝ)) ∧
((1804737/100000:ℝ)≤Real.exp (2893/1000:ℝ)∧Real.exp (2893/1000:ℝ)≤(902369/50000:ℝ)) ∧
((252453/25000:ℝ)≤Real.exp (46247/20000:ℝ)∧Real.exp (46247/20000:ℝ)≤(1009813/100000:ℝ)) ∧
((1652261/100000:ℝ)≤Real.exp (280473/100000:ℝ)∧Real.exp (280473/100000:ℝ)≤(826131/50000:ℝ)) ∧
((881901/100000:ℝ)≤Real.exp (217691/100000:ℝ)∧Real.exp (217691/100000:ℝ)≤(440951/50000:ℝ)) ∧
((1678977/100000:ℝ)≤Real.exp (282077/100000:ℝ)∧Real.exp (282077/100000:ℝ)≤(839489/50000:ℝ)) := by
 exact ⟨EmlComplexity.ExpBoundsProof_large.p1,⟨EmlComplexity.ExpBoundsProof_large.p4,⟨EmlComplexity.ExpBoundsProof_large.p6,⟨EmlComplexity.ExpBoundsProof_large.p7,⟨EmlComplexity.ExpBoundsProof_large.p8,⟨EmlComplexity.ExpBoundsProof_large.p13,⟨EmlComplexity.ExpBoundsProof_large.p14,⟨EmlComplexity.ExpBoundsProof_large.p15,⟨EmlComplexity.ExpBoundsProof_large.p16,⟨EmlComplexity.ExpBoundsProof_large.p23,⟨EmlComplexity.ExpBoundsProof_large.p27,⟨EmlComplexity.ExpBoundsProof_large.p29,⟨EmlComplexity.ExpBoundsProof_large.p34,⟨EmlComplexity.ExpBoundsProof_large.p35,⟨EmlComplexity.ExpBoundsProof_large.p36,⟨EmlComplexity.ExpBoundsProof_large.p39,⟨EmlComplexity.ExpBoundsProof_large.p42,⟨EmlComplexity.ExpBoundsProof_large.p48,⟨EmlComplexity.ExpBoundsProof_large.p63,⟨EmlComplexity.ExpBoundsProof_large.p65,⟨EmlComplexity.ExpBoundsProof_large.p67,⟨EmlComplexity.ExpBoundsProof_large.p73,⟨EmlComplexity.ExpBoundsProof_large.p74,⟨EmlComplexity.ExpBoundsProof_large.p77,⟨EmlComplexity.ExpBoundsProof_large.p78,⟨EmlComplexity.ExpBoundsProof_large.p79,⟨EmlComplexity.ExpBoundsProof_large.p80,⟨EmlComplexity.ExpBoundsProof_large.p81,⟨EmlComplexity.ExpBoundsProof_large.p83,⟨EmlComplexity.ExpBoundsProof_large.p84,⟨EmlComplexity.ExpBoundsProof_large.p90,⟨EmlComplexity.ExpBoundsProof_large.p100,⟨EmlComplexity.ExpBoundsProof_large.p113,⟨EmlComplexity.ExpBoundsProof_large.p126,⟨EmlComplexity.ExpBoundsProof_large.p153,⟨EmlComplexity.ExpBoundsProof_large.p155,⟨EmlComplexity.ExpBoundsProof_large.p157,⟨EmlComplexity.ExpBoundsProof_large.p159,⟨EmlComplexity.ExpBoundsProof_large.p160,⟨EmlComplexity.ExpBoundsProof_large.p162,⟨EmlComplexity.ExpBoundsProof_large.p164,⟨EmlComplexity.ExpBoundsProof_large.p172,⟨EmlComplexity.ExpBoundsProof_large.p184,⟨EmlComplexity.ExpBoundsProof_large.p187,⟨EmlComplexity.ExpBoundsProof_large.p188,⟨EmlComplexity.ExpBoundsProof_large.p189,⟨EmlComplexity.ExpBoundsProof_large.p190,⟨EmlComplexity.ExpBoundsProof_large.p191,⟨EmlComplexity.ExpBoundsProof_large.p192,⟨EmlComplexity.ExpBoundsProof_large.p193,⟨EmlComplexity.ExpBoundsProof_large.p194,⟨EmlComplexity.ExpBoundsProof_large.p195,⟨EmlComplexity.ExpBoundsProof_large.p196,⟨EmlComplexity.ExpBoundsProof_large.p197,⟨EmlComplexity.ExpBoundsProof_large.p198,⟨EmlComplexity.ExpBoundsProof_large.p200,⟨EmlComplexity.ExpBoundsProof_large.p201,⟨EmlComplexity.ExpBoundsProof_large.p202,⟨EmlComplexity.ExpBoundsProof_large.p203,⟨EmlComplexity.ExpBoundsProof_large.p206,⟨EmlComplexity.ExpBoundsProof_large.p211,⟨EmlComplexity.ExpBoundsProof_large.p225,⟨EmlComplexity.ExpBoundsProof_large.p228,⟨EmlComplexity.ExpBoundsProof_large.p233,⟨EmlComplexity.ExpBoundsProof_large.p234,⟨EmlComplexity.ExpBoundsProof_large.p239,⟨EmlComplexity.ExpBoundsProof_large.p240,⟨EmlComplexity.ExpBoundsProof_large.p241,⟨EmlComplexity.ExpBoundsProof_large.p269,⟨EmlComplexity.ExpBoundsProof_large.p270,⟨EmlComplexity.ExpBoundsProof_large.p283,⟨EmlComplexity.ExpBoundsProof_large.p289,⟨EmlComplexity.ExpBoundsProof_large.p300,EmlComplexity.ExpBoundsProof_large.p312⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms solution
