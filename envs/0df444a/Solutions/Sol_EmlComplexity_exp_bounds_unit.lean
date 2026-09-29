-- Prove2me | solution 1 for EmlComplexity.exp_bounds_unit
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T08:07:18.671008+00:00
-- url     : https://prove2.me/submissions/b87acef2-3d57-4774-bcfb-b7fa743f5fcc

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace EmlComplexity.ExpBoundsProof_unit
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
lemma p2:(17183/10000:ℝ)≤Real.exp (27067/50000:ℝ)∧Real.exp (27067/50000:ℝ)≤(171831/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(27067/100000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(27067/100000:ℝ)) (l:=(1310841/1000000:ℝ)) (u:=(1310843/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p5:(217691/100000:ℝ)≤Real.exp (77791/100000:ℝ)∧Real.exp (77791/100000:ℝ)≤(54423/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(77791/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(77791/200000:ℝ)) (l:=(36885939/25000000:ℝ)) (u:=(73771909/50000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p9:(194041/100000:ℝ)≤Real.exp (6629/10000:ℝ)∧Real.exp (6629/10000:ℝ)≤(97021/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(6629/20000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(6629/20000:ℝ)) (l:=(13929863/10000000:ℝ)) (u:=(139298651/100000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p10:(6873/4000:ℝ)≤Real.exp (54131/100000:ℝ)∧Real.exp (54131/100000:ℝ)≤(85913/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(54131/200000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(54131/200000:ℝ)) (l:=(1310821/1000000:ℝ)) (u:=(1310823/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p11:(2177/1000:ℝ)≤Real.exp (15559/20000:ℝ)∧Real.exp (15559/20000:ℝ)≤(217701/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(15559/40000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(15559/40000:ℝ)) (l:=(1475467/1000000:ℝ)) (u:=(368867/250000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p18:(1001/1000:ℝ)≤Real.exp (1/1000:ℝ)∧Real.exp (1/1000:ℝ)≤(100101/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(1/1000:ℝ)) (by norm_num) (n:=3) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1/1000:ℝ)) (l:=(1001/1000:ℝ)) (u:=(1001001/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p21:(107067/100000:ℝ)≤Real.exp (6829/100000:ℝ)∧Real.exp (6829/100000:ℝ)≤(26767/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(6829/100000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(6829/100000:ℝ)) (l:=(1070673/1000000:ℝ)) (u:=(267669/250000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p24:(41107/20000:ℝ)≤Real.exp (14409/20000:ℝ)∧Real.exp (14409/20000:ℝ)≤(6423/3125:ℝ):=by
 have h:=Real.exp_bound (x:=(14409/40000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(14409/40000:ℝ)) (l:=(1433651/1000000:ℝ)) (u:=(358413/250000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p30:(119773/100000:ℝ)≤Real.exp (18043/100000:ℝ)∧Real.exp (18043/100000:ℝ)≤(59887/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(18043/100000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(18043/100000:ℝ)) (l:=(299433/250000:ℝ)) (u:=(1197733/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p40:(105127/100000:ℝ)≤Real.exp (1/20:ℝ)∧Real.exp (1/20:ℝ)≤(13141/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(1/20:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1/20:ℝ)) (l:=(105127/100000:ℝ)) (u:=(131409/125000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p43:(103707/100000:ℝ)≤Real.exp (91/2500:ℝ)∧Real.exp (91/2500:ℝ)≤(25927/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(91/2500:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(91/2500:ℝ)) (l:=(103707/100000:ℝ)) (u:=(1037071/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p44:(6093/5000:ℝ)≤Real.exp (19771/100000:ℝ)∧Real.exp (19771/100000:ℝ)≤(121861/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(19771/100000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(19771/100000:ℝ)) (l:=(1218603/1000000:ℝ)) (u:=(121861/100000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p50:(53531/50000:ℝ)≤Real.exp (853/12500:ℝ)∧Real.exp (853/12500:ℝ)≤(107063/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(853/12500:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(853/12500:ℝ)) (l:=(53531/50000:ℝ)) (u:=(1070623/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p51:(100001/100000:ℝ)≤Real.exp (1/100000:ℝ)∧Real.exp (1/100000:ℝ)≤(50001/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(1/100000:ℝ)) (by norm_num) (n:=3) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1/100000:ℝ)) (l:=(100001/100000:ℝ)) (u:=(1000011/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p52:(99893/50000:ℝ)≤Real.exp (8651/12500:ℝ)∧Real.exp (8651/12500:ℝ)≤(199787/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(8651/25000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(8651/25000:ℝ)) (l:=(706729/500000:ℝ)) (u:=(70673/50000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p53:(194029/100000:ℝ)≤Real.exp (16571/25000:ℝ)∧Real.exp (16571/25000:ℝ)≤(19403/10000:ℝ):=by
 have h:=Real.exp_bound (x:=(16571/50000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(16571/50000:ℝ)) (l:=(87059/62500:ℝ)) (u:=(278589/200000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p54:(51387/25000:ℝ)≤Real.exp (72051/100000:ℝ)∧Real.exp (72051/100000:ℝ)≤(205549/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(72051/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(72051/200000:ℝ)) (l:=(143369461/100000000:ℝ)) (u:=(71684749/50000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p55:(2063/2000:ℝ)≤Real.exp (1551/50000:ℝ)∧Real.exp (1551/50000:ℝ)≤(103151/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(1551/50000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1551/50000:ℝ)) (l:=(515753/500000:ℝ)) (u:=(1031507/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p60:(12689/5000:ℝ)≤Real.exp (9313/10000:ℝ)∧Real.exp (9313/10000:ℝ)≤(253781/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(9313/20000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(9313/20000:ℝ)) (l:=(1593049/1000000:ℝ)) (u:=(31861/20000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p68:(110219/100000:ℝ)≤Real.exp (973/10000:ℝ)∧Real.exp (973/10000:ℝ)≤(5511/5000:ℝ):=by
 have h:=Real.exp_bound (x:=(973/10000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(973/10000:ℝ)) (l:=(110219/100000:ℝ)) (u:=(1102191/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p70:(166869/100000:ℝ)≤Real.exp (12801/25000:ℝ)∧Real.exp (12801/25000:ℝ)≤(16687/10000:ℝ):=by
 have h:=Real.exp_bound (x:=(12801/50000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(12801/50000:ℝ)) (l:=(645889/500000:ℝ)) (u:=(1291779/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p76:(132497/50000:ℝ)≤Real.exp (48727/50000:ℝ)∧Real.exp (48727/50000:ℝ)≤(52999/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(48727/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(48727/100000:ℝ)) (l:=(16278659/10000000:ℝ)) (u:=(10174163/6250000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p88:(20201/20000:ℝ)≤Real.exp (1/100:ℝ)∧Real.exp (1/100:ℝ)≤(50503/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(1/100:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1/100:ℝ)) (l:=(20201/20000:ℝ)) (u:=(1010051/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p95:(110517/100000:ℝ)≤Real.exp (1/10:ℝ)∧Real.exp (1/10:ℝ)≤(55259/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(1/10:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1/10:ℝ)) (l:=(110517/100000:ℝ)) (u:=(1105171/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p101:(52707/50000:ℝ)≤Real.exp (5273/100000:ℝ)∧Real.exp (5273/100000:ℝ)≤(21083/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(5273/100000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(5273/100000:ℝ)) (l:=(16471/15625:ℝ)) (u:=(527073/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p102:(30299/25000:ℝ)≤Real.exp (2403/12500:ℝ)∧Real.exp (2403/12500:ℝ)≤(121197/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(2403/12500:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(2403/12500:ℝ)) (l:=(1211961/1000000:ℝ)) (u:=(605981/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p103:(112791/100000:ℝ)≤Real.exp (12037/100000:ℝ)∧Real.exp (12037/100000:ℝ)≤(14099/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(12037/100000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(12037/100000:ℝ)) (l:=(1127913/1000000:ℝ)) (u:=(225583/200000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p106:(19381/10000:ℝ)≤Real.exp (66171/100000:ℝ)∧Real.exp (66171/100000:ℝ)≤(193811/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(66171/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(66171/200000:ℝ)) (l:=(1392157/1000000:ℝ)) (u:=(696079/500000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p115:(791/500:ℝ)≤Real.exp (45869/100000:ℝ)∧Real.exp (45869/100000:ℝ)≤(158201/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(45869/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(45869/100000:ℝ)) (l:=(791/500:ℝ)) (u:=(1582001/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p117:(107323/100000:ℝ)≤Real.exp (1767/25000:ℝ)∧Real.exp (1767/25000:ℝ)≤(26831/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(1767/25000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1767/25000:ℝ)) (l:=(214647/200000:ℝ)) (u:=(536619/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p120:(103701/100000:ℝ)≤Real.exp (727/20000:ℝ)∧Real.exp (727/20000:ℝ)≤(51851/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(727/20000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(727/20000:ℝ)) (l:=(518509/500000:ℝ)) (u:=(1037019/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p122:(60927/50000:ℝ)≤Real.exp (9883/50000:ℝ)∧Real.exp (9883/50000:ℝ)≤(24371/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(9883/50000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(9883/50000:ℝ)) (l:=(609271/500000:ℝ)) (u:=(1218549/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p124:(100001/100000:ℝ)≤Real.exp (10801/1000000000:ℝ)∧Real.exp (10801/1000000000:ℝ)≤(50001/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(10801/1000000000:ℝ)) (by norm_num) (n:=2) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(10801/1000000000:ℝ)) (l:=(100001/100000:ℝ)) (u:=(1000011/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p125:(52957/50000:ℝ)≤Real.exp (28731/500000:ℝ)∧Real.exp (28731/500000:ℝ)≤(21183/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(28731/500000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(28731/500000:ℝ)) (l:=(1059143/1000000:ℝ)) (u:=(529573/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p127:(1:ℝ)≤Real.exp 0∧Real.exp 0≤1:=by norm_num
lemma p128:(99887/50000:ℝ)≤Real.exp (34601/50000:ℝ)∧Real.exp (34601/50000:ℝ)≤(7991/4000:ℝ):=by
 have h:=Real.exp_bound (x:=(34601/100000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(34601/100000:ℝ)) (l:=(176677/125000:ℝ)) (u:=(1413417/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p129:(202629/100000:ℝ)≤Real.exp (70621/100000:ℝ)∧Real.exp (70621/100000:ℝ)≤(20263/10000:ℝ):=by
 have h:=Real.exp_bound (x:=(70621/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(70621/200000:ℝ)) (l:=(35587/25000:ℝ)) (u:=(1423481/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p130:(134361/50000:ℝ)≤Real.exp (98851/100000:ℝ)∧Real.exp (98851/100000:ℝ)≤(268723/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(98851/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(98851/200000:ℝ)) (l:=(409819/250000:ℝ)) (u:=(1639277/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p134:(125063/100000:ℝ)≤Real.exp (4473/20000:ℝ)∧Real.exp (4473/20000:ℝ)≤(15633/12500:ℝ):=by
 have h:=Real.exp_bound (x:=(4473/20000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(4473/20000:ℝ)) (l:=(156329/125000:ℝ)) (u:=(625317/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p137:(89351/50000:ℝ)≤Real.exp (11611/20000:ℝ)∧Real.exp (11611/20000:ℝ)≤(178703/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(11611/40000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(11611/40000:ℝ)) (l:=(66839749/50000000:ℝ)) (u:=(66839753/50000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p138:(119763/100000:ℝ)≤Real.exp (3607/20000:ℝ)∧Real.exp (3607/20000:ℝ)≤(29941/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(3607/20000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(3607/20000:ℝ)) (l:=(18713/15625:ℝ)) (u:=(1197637/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p139:(126899/50000:ℝ)≤Real.exp (93137/100000:ℝ)∧Real.exp (93137/100000:ℝ)≤(253799/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(93137/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(93137/200000:ℝ)) (l:=(99569/62500:ℝ)) (u:=(796553/500000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p140:(37869/25000:ℝ)≤Real.exp (20763/50000:ℝ)∧Real.exp (20763/50000:ℝ)≤(151477/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(20763/50000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(20763/50000:ℝ)) (l:=(1514763/1000000:ℝ)) (u:=(302953/200000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p146:(262093/100000:ℝ)≤Real.exp (96353/100000:ℝ)∧Real.exp (96353/100000:ℝ)≤(131047/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(96353/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(96353/200000:ℝ)) (l:=(1618929/1000000:ℝ)) (u:=(161893/100000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p147:(220619/100000:ℝ)≤Real.exp (79127/100000:ℝ)∧Real.exp (79127/100000:ℝ)≤(11031/5000:ℝ):=by
 have h:=Real.exp_bound (x:=(79127/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(79127/200000:ℝ)) (l:=(742663/500000:ℝ)) (u:=(92833/62500:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p150:(174377/100000:ℝ)≤Real.exp (11121/20000:ℝ)∧Real.exp (11121/20000:ℝ)≤(87189/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(11121/40000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(11121/40000:ℝ)) (l:=(1320519/1000000:ℝ)) (u:=(33013/25000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p151:(16563/6250:ℝ)≤Real.exp (97459/100000:ℝ)∧Real.exp (97459/100000:ℝ)≤(265009/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(97459/200000:ℝ)) (by norm_num) (n:=9) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(97459/200000:ℝ)) (l:=(40697669/25000000:ℝ)) (u:=(81395339/50000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p165:(57517/50000:ℝ)≤Real.exp (7003/50000:ℝ)∧Real.exp (7003/50000:ℝ)≤(23007/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(7003/50000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(7003/50000:ℝ)) (l:=(1150341/1000000:ℝ)) (u:=(1150343/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p167:(41127/25000:ℝ)≤Real.exp (49779/100000:ℝ)∧Real.exp (49779/100000:ℝ)≤(164509/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(49779/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(49779/100000:ℝ)) (l:=(1645081/1000000:ℝ)) (u:=(822541/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p169:(136853/100000:ℝ)≤Real.exp (15687/50000:ℝ)∧Real.exp (15687/50000:ℝ)≤(68427/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(15687/50000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(15687/50000:ℝ)) (l:=(136853/100000:ℝ)) (u:=(273707/200000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p181:(53637/20000:ℝ)≤Real.exp (98651/100000:ℝ)∧Real.exp (98651/100000:ℝ)≤(134093/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(98651/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(98651/200000:ℝ)) (l:=(163763787/100000000:ℝ)) (u:=(5117619/3125000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p182:(252053/100000:ℝ)≤Real.exp (92447/100000:ℝ)∧Real.exp (92447/100000:ℝ)≤(126027/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(92447/200000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(92447/200000:ℝ)) (l:=(793809/500000:ℝ)) (u:=(1587619/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p183:(152063/100000:ℝ)≤Real.exp (41913/100000:ℝ)∧Real.exp (41913/100000:ℝ)≤(4752/3125:ℝ):=by
 have h:=Real.exp_bound (x:=(41913/100000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(41913/100000:ℝ)) (l:=(1520637/1000000:ℝ)) (u:=(1520639/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p185:(164769/100000:ℝ)≤Real.exp (24969/50000:ℝ)∧Real.exp (24969/50000:ℝ)≤(16477/10000:ℝ):=by
 have h:=Real.exp_bound (x:=(24969/50000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(24969/50000:ℝ)) (l:=(329539/200000:ℝ)) (u:=(16477/10000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p186:(135911/50000:ℝ)≤Real.exp (49999/50000:ℝ)∧Real.exp (49999/50000:ℝ)≤(271823/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(49999/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(49999/100000:ℝ)) (l:=(25761/15625:ℝ)) (u:=(329741/200000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p199:(100101/100000:ℝ)≤Real.exp (101/100000:ℝ)∧Real.exp (101/100000:ℝ)≤(50051/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(101/100000:ℝ)) (by norm_num) (n:=3) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(101/100000:ℝ)) (l:=(100101/100000:ℝ)) (u:=(1001011/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p215:(64201/50000:ℝ)≤Real.exp (1/4:ℝ)∧Real.exp (1/4:ℝ)≤(128403/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(1/4:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1/4:ℝ)) (l:=(160503/125000:ℝ)) (u:=(642013/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p223:(231231/100000:ℝ)≤Real.exp (3353/4000:ℝ)∧Real.exp (3353/4000:ℝ)≤(7226/3125:ℝ):=by
 have h:=Real.exp_bound (x:=(3353/8000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(3353/8000:ℝ)) (l:=(1520629/1000000:ℝ)) (u:=(1520631/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p226:(191739/100000:ℝ)≤Real.exp (65097/100000:ℝ)∧Real.exp (65097/100000:ℝ)≤(9587/5000:ℝ):=by
 have h:=Real.exp_bound (x:=(65097/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(65097/200000:ℝ)) (l:=(138470189/100000000:ℝ)) (u:=(2163597/1562500:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p235:(25119/10000:ℝ)≤Real.exp (11513/12500:ℝ)∧Real.exp (11513/12500:ℝ)≤(251191/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(11513/25000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(11513/25000:ℝ)) (l:=(7924489/5000000:ℝ)) (u:=(158489793/100000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p243:(3268/3125:ℝ)≤Real.exp (179/4000:ℝ)∧Real.exp (179/4000:ℝ)≤(104577/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(179/4000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(179/4000:ℝ)) (l:=(522883/500000:ℝ)) (u:=(1045767/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p245:(24301/20000:ℝ)≤Real.exp (19479/100000:ℝ)∧Real.exp (19479/100000:ℝ)≤(60753/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(19479/100000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(19479/100000:ℝ)) (l:=(24301/20000:ℝ)) (u:=(1215057/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p246:(59977/50000:ℝ)≤Real.exp (9097/50000:ℝ)∧Real.exp (9097/50000:ℝ)≤(23991/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(9097/50000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(9097/50000:ℝ)) (l:=(599771/500000:ℝ)) (u:=(1199543/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p247:(27789/25000:ℝ)≤Real.exp (10577/100000:ℝ)∧Real.exp (10577/100000:ℝ)≤(111157/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(10577/100000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(10577/100000:ℝ)) (l:=(222313/200000:ℝ)) (u:=(1111567/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p248:(58389/50000:ℝ)≤Real.exp (15511/100000:ℝ)∧Real.exp (15511/100000:ℝ)≤(116779/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(15511/100000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(15511/100000:ℝ)) (l:=(145973/125000:ℝ)) (u:=(1167787/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p249:(158203/100000:ℝ)≤Real.exp (45871/100000:ℝ)∧Real.exp (45871/100000:ℝ)≤(39551/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(45871/100000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(45871/100000:ℝ)) (l:=(1582031/1000000:ℝ)) (u:=(98877/62500:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p253:(5721/3125:ℝ)≤Real.exp (60471/100000:ℝ)∧Real.exp (60471/100000:ℝ)≤(183073/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(60471/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(60471/200000:ℝ)) (l:=(135304137/100000000:ℝ)) (u:=(33826037/25000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p254:(24837/10000:ℝ)≤Real.exp (3639/4000:ℝ)∧Real.exp (3639/4000:ℝ)≤(248371/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(3639/8000:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(3639/8000:ℝ)) (l:=(196997/125000:ℝ)) (u:=(1575977/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p256:(127101/50000:ℝ)≤Real.exp (5831/6250:ℝ)∧Real.exp (5831/6250:ℝ)≤(254203/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(5831/12500:ℝ)) (by norm_num) (n:=8) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(5831/12500:ℝ)) (l:=(159437199/100000000:ℝ)) (u:=(39859303/25000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p274:(31217/25000:ℝ)≤Real.exp (22209/100000:ℝ)∧Real.exp (22209/100000:ℝ)≤(124869/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(22209/100000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(22209/100000:ℝ)) (l:=(1248683/1000000:ℝ)) (u:=(312171/250000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p277:(84893/50000:ℝ)≤Real.exp (52937/100000:ℝ)∧Real.exp (52937/100000:ℝ)≤(169787/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(52937/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(52937/200000:ℝ)) (l:=(65151/50000:ℝ)) (u:=(1303021/1000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p281:(103777/100000:ℝ)≤Real.exp (927/25000:ℝ)∧Real.exp (927/25000:ℝ)≤(51889/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(927/25000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(927/25000:ℝ)) (l:=(41511/40000:ℝ)) (u:=(1037777/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p282:(62217/50000:ℝ)≤Real.exp (21861/100000:ℝ)∧Real.exp (21861/100000:ℝ)≤(24887/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(21861/100000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(21861/100000:ℝ)) (l:=(248869/200000:ℝ)) (u:=(622173/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p284:(51271/25000:ℝ)≤Real.exp (2873/4000:ℝ)∧Real.exp (2873/4000:ℝ)≤(41017/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(2873/8000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(2873/8000:ℝ)) (l:=(71603773/50000000:ℝ)) (u:=(71603791/50000000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p288:(50001/50000:ℝ)≤Real.exp (1/50000:ℝ)∧Real.exp (1/50000:ℝ)≤(100003/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(1/50000:ℝ)) (by norm_num) (n:=3) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1/50000:ℝ)) (l:=(50001/50000:ℝ)) (u:=(1000021/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p291:(3294/3125:ℝ)≤Real.exp (5267/100000:ℝ)∧Real.exp (5267/100000:ℝ)≤(105409/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(5267/100000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(5267/100000:ℝ)) (l:=(1054081/1000000:ℝ)) (u:=(527041/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p293:(12119/10000:ℝ)≤Real.exp (19219/100000:ℝ)∧Real.exp (19219/100000:ℝ)≤(121191/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(19219/100000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(19219/100000:ℝ)) (l:=(12119/10000:ℝ)) (u:=(1211901/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p295:(22557/20000:ℝ)≤Real.exp (376/3125:ℝ)∧Real.exp (376/3125:ℝ)≤(56393/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(376/3125:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(376/3125:ℝ)) (l:=(1127857/1000000:ℝ)) (u:=(563929/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p297:(96897/50000:ℝ)≤Real.exp (66163/100000:ℝ)∧Real.exp (66163/100000:ℝ)≤(38759/20000:ℝ):=by
 have h:=Real.exp_bound (x:=(66163/200000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(66163/200000:ℝ)) (l:=(34802551/25000000:ℝ)) (u:=(8700639/6250000:ℝ)) (n:=2)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p298:(100001/100000:ℝ)≤Real.exp (2703/250000000:ℝ)∧Real.exp (2703/250000000:ℝ)≤(50001/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(2703/250000000:ℝ)) (by norm_num) (n:=2) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(2703/250000000:ℝ)) (l:=(100001/100000:ℝ)) (u:=(1000011/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p299:(53113/50000:ℝ)≤Real.exp (7551/125000:ℝ)∧Real.exp (7551/125000:ℝ)≤(106227/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(7551/125000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(7551/125000:ℝ)) (l:=(265567/250000:ℝ)) (u:=(106227/100000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p301:(1:ℝ)≤Real.exp (4267/625000000:ℝ)∧Real.exp (4267/625000000:ℝ)≤(100001/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(4267/625000000:ℝ)) (by norm_num) (n:=2) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(4267/625000000:ℝ)) (l:=(500003/500000:ℝ)) (u:=(1000007/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p302:(50003/50000:ℝ)≤Real.exp (15053/250000000:ℝ)∧Real.exp (15053/250000000:ℝ)≤(100007/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(15053/250000000:ℝ)) (by norm_num) (n:=2) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(15053/250000000:ℝ)) (l:=(50003/50000:ℝ)) (u:=(1000061/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p303:(23381/20000:ℝ)≤Real.exp (781/5000:ℝ)∧Real.exp (781/5000:ℝ)≤(58453/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(781/5000:ℝ)) (by norm_num) (n:=6) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(781/5000:ℝ)) (l:=(1169059/1000000:ℝ)) (u:=(58453/50000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p304:(3132/3125:ℝ)≤Real.exp (22407/10000000:ℝ)∧Real.exp (22407/10000000:ℝ)≤(4009/4000:ℝ):=by
 have h:=Real.exp_bound (x:=(22407/10000000:ℝ)) (by norm_num) (n:=3) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(22407/10000000:ℝ)) (l:=(1002243/1000000:ℝ)) (u:=(250561/250000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p305:(50003/50000:ℝ)≤Real.exp (1383/20000000:ℝ)∧Real.exp (1383/20000000:ℝ)≤(100007/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(1383/20000000:ℝ)) (by norm_num) (n:=2) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(1383/20000000:ℝ)) (l:=(1000069/1000000:ℝ)) (u:=(100007/100000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p307:(31639/20000:ℝ)≤Real.exp (22933/50000:ℝ)∧Real.exp (22933/50000:ℝ)≤(39549/25000:ℝ):=by
 have h:=Real.exp_bound (x:=(22933/50000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(22933/50000:ℝ)) (l:=(31639/20000:ℝ)) (u:=(1581953/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p308:(119647/100000:ℝ)≤Real.exp (8969/50000:ℝ)∧Real.exp (8969/50000:ℝ)≤(3739/3125:ℝ):=by
 have h:=Real.exp_bound (x:=(8969/50000:ℝ)) (by norm_num) (n:=5) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(8969/50000:ℝ)) (l:=(1196471/1000000:ℝ)) (u:=(299119/250000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p310:(107317/100000:ℝ)≤Real.exp (3531/50000:ℝ)∧Real.exp (3531/50000:ℝ)≤(53659/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(3531/50000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(3531/50000:ℝ)) (l:=(107317/100000:ℝ)) (u:=(536587/500000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p311:(36117/25000:ℝ)≤Real.exp (36789/100000:ℝ)∧Real.exp (36789/100000:ℝ)≤(144469/100000:ℝ):=by
 have h:=Real.exp_bound (x:=(36789/100000:ℝ)) (by norm_num) (n:=7) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(36789/100000:ℝ)) (l:=(722341/500000:ℝ)) (u:=(361171/250000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p314:(100001/100000:ℝ)≤Real.exp (5399/500000000:ℝ)∧Real.exp (5399/500000000:ℝ)≤(50001/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(5399/500000000:ℝ)) (by norm_num) (n:=2) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(5399/500000000:ℝ)) (l:=(100001/100000:ℝ)) (u:=(1000011/1000000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
lemma p317:(105913/100000:ℝ)≤Real.exp (57457/1000000:ℝ)∧Real.exp (57457/1000000:ℝ)≤(52957/50000:ℝ):=by
 have h:=Real.exp_bound (x:=(57457/1000000:ℝ)) (by norm_num) (n:=4) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 have h':=abs_sub_le_iff.mp h
 apply scaled_interval (r:=(57457/1000000:ℝ)) (l:=(529569/500000:ℝ)) (u:=(52957/50000:ℝ)) (n:=1)
 · norm_num
 · constructor <;> linarith only [h'.1,h'.2]
 · norm_num
 · norm_num
 · norm_num
end EmlComplexity.ExpBoundsProof_unit

theorem solution :
((17183/10000:ℝ)≤Real.exp (27067/50000:ℝ)∧Real.exp (27067/50000:ℝ)≤(171831/100000:ℝ)) ∧
((217691/100000:ℝ)≤Real.exp (77791/100000:ℝ)∧Real.exp (77791/100000:ℝ)≤(54423/25000:ℝ)) ∧
((194041/100000:ℝ)≤Real.exp (6629/10000:ℝ)∧Real.exp (6629/10000:ℝ)≤(97021/50000:ℝ)) ∧
((6873/4000:ℝ)≤Real.exp (54131/100000:ℝ)∧Real.exp (54131/100000:ℝ)≤(85913/50000:ℝ)) ∧
((2177/1000:ℝ)≤Real.exp (15559/20000:ℝ)∧Real.exp (15559/20000:ℝ)≤(217701/100000:ℝ)) ∧
((1001/1000:ℝ)≤Real.exp (1/1000:ℝ)∧Real.exp (1/1000:ℝ)≤(100101/100000:ℝ)) ∧
((107067/100000:ℝ)≤Real.exp (6829/100000:ℝ)∧Real.exp (6829/100000:ℝ)≤(26767/25000:ℝ)) ∧
((41107/20000:ℝ)≤Real.exp (14409/20000:ℝ)∧Real.exp (14409/20000:ℝ)≤(6423/3125:ℝ)) ∧
((119773/100000:ℝ)≤Real.exp (18043/100000:ℝ)∧Real.exp (18043/100000:ℝ)≤(59887/50000:ℝ)) ∧
((105127/100000:ℝ)≤Real.exp (1/20:ℝ)∧Real.exp (1/20:ℝ)≤(13141/12500:ℝ)) ∧
((103707/100000:ℝ)≤Real.exp (91/2500:ℝ)∧Real.exp (91/2500:ℝ)≤(25927/25000:ℝ)) ∧
((6093/5000:ℝ)≤Real.exp (19771/100000:ℝ)∧Real.exp (19771/100000:ℝ)≤(121861/100000:ℝ)) ∧
((53531/50000:ℝ)≤Real.exp (853/12500:ℝ)∧Real.exp (853/12500:ℝ)≤(107063/100000:ℝ)) ∧
((100001/100000:ℝ)≤Real.exp (1/100000:ℝ)∧Real.exp (1/100000:ℝ)≤(50001/50000:ℝ)) ∧
((99893/50000:ℝ)≤Real.exp (8651/12500:ℝ)∧Real.exp (8651/12500:ℝ)≤(199787/100000:ℝ)) ∧
((194029/100000:ℝ)≤Real.exp (16571/25000:ℝ)∧Real.exp (16571/25000:ℝ)≤(19403/10000:ℝ)) ∧
((51387/25000:ℝ)≤Real.exp (72051/100000:ℝ)∧Real.exp (72051/100000:ℝ)≤(205549/100000:ℝ)) ∧
((2063/2000:ℝ)≤Real.exp (1551/50000:ℝ)∧Real.exp (1551/50000:ℝ)≤(103151/100000:ℝ)) ∧
((12689/5000:ℝ)≤Real.exp (9313/10000:ℝ)∧Real.exp (9313/10000:ℝ)≤(253781/100000:ℝ)) ∧
((110219/100000:ℝ)≤Real.exp (973/10000:ℝ)∧Real.exp (973/10000:ℝ)≤(5511/5000:ℝ)) ∧
((166869/100000:ℝ)≤Real.exp (12801/25000:ℝ)∧Real.exp (12801/25000:ℝ)≤(16687/10000:ℝ)) ∧
((132497/50000:ℝ)≤Real.exp (48727/50000:ℝ)∧Real.exp (48727/50000:ℝ)≤(52999/20000:ℝ)) ∧
((20201/20000:ℝ)≤Real.exp (1/100:ℝ)∧Real.exp (1/100:ℝ)≤(50503/50000:ℝ)) ∧
((110517/100000:ℝ)≤Real.exp (1/10:ℝ)∧Real.exp (1/10:ℝ)≤(55259/50000:ℝ)) ∧
((52707/50000:ℝ)≤Real.exp (5273/100000:ℝ)∧Real.exp (5273/100000:ℝ)≤(21083/20000:ℝ)) ∧
((30299/25000:ℝ)≤Real.exp (2403/12500:ℝ)∧Real.exp (2403/12500:ℝ)≤(121197/100000:ℝ)) ∧
((112791/100000:ℝ)≤Real.exp (12037/100000:ℝ)∧Real.exp (12037/100000:ℝ)≤(14099/12500:ℝ)) ∧
((19381/10000:ℝ)≤Real.exp (66171/100000:ℝ)∧Real.exp (66171/100000:ℝ)≤(193811/100000:ℝ)) ∧
((791/500:ℝ)≤Real.exp (45869/100000:ℝ)∧Real.exp (45869/100000:ℝ)≤(158201/100000:ℝ)) ∧
((107323/100000:ℝ)≤Real.exp (1767/25000:ℝ)∧Real.exp (1767/25000:ℝ)≤(26831/25000:ℝ)) ∧
((103701/100000:ℝ)≤Real.exp (727/20000:ℝ)∧Real.exp (727/20000:ℝ)≤(51851/50000:ℝ)) ∧
((60927/50000:ℝ)≤Real.exp (9883/50000:ℝ)∧Real.exp (9883/50000:ℝ)≤(24371/20000:ℝ)) ∧
((100001/100000:ℝ)≤Real.exp (10801/1000000000:ℝ)∧Real.exp (10801/1000000000:ℝ)≤(50001/50000:ℝ)) ∧
((52957/50000:ℝ)≤Real.exp (28731/500000:ℝ)∧Real.exp (28731/500000:ℝ)≤(21183/20000:ℝ)) ∧
((1:ℝ)≤Real.exp 0∧Real.exp 0≤1) ∧
((99887/50000:ℝ)≤Real.exp (34601/50000:ℝ)∧Real.exp (34601/50000:ℝ)≤(7991/4000:ℝ)) ∧
((202629/100000:ℝ)≤Real.exp (70621/100000:ℝ)∧Real.exp (70621/100000:ℝ)≤(20263/10000:ℝ)) ∧
((134361/50000:ℝ)≤Real.exp (98851/100000:ℝ)∧Real.exp (98851/100000:ℝ)≤(268723/100000:ℝ)) ∧
((125063/100000:ℝ)≤Real.exp (4473/20000:ℝ)∧Real.exp (4473/20000:ℝ)≤(15633/12500:ℝ)) ∧
((89351/50000:ℝ)≤Real.exp (11611/20000:ℝ)∧Real.exp (11611/20000:ℝ)≤(178703/100000:ℝ)) ∧
((119763/100000:ℝ)≤Real.exp (3607/20000:ℝ)∧Real.exp (3607/20000:ℝ)≤(29941/25000:ℝ)) ∧
((126899/50000:ℝ)≤Real.exp (93137/100000:ℝ)∧Real.exp (93137/100000:ℝ)≤(253799/100000:ℝ)) ∧
((37869/25000:ℝ)≤Real.exp (20763/50000:ℝ)∧Real.exp (20763/50000:ℝ)≤(151477/100000:ℝ)) ∧
((262093/100000:ℝ)≤Real.exp (96353/100000:ℝ)∧Real.exp (96353/100000:ℝ)≤(131047/50000:ℝ)) ∧
((220619/100000:ℝ)≤Real.exp (79127/100000:ℝ)∧Real.exp (79127/100000:ℝ)≤(11031/5000:ℝ)) ∧
((174377/100000:ℝ)≤Real.exp (11121/20000:ℝ)∧Real.exp (11121/20000:ℝ)≤(87189/50000:ℝ)) ∧
((16563/6250:ℝ)≤Real.exp (97459/100000:ℝ)∧Real.exp (97459/100000:ℝ)≤(265009/100000:ℝ)) ∧
((57517/50000:ℝ)≤Real.exp (7003/50000:ℝ)∧Real.exp (7003/50000:ℝ)≤(23007/20000:ℝ)) ∧
((41127/25000:ℝ)≤Real.exp (49779/100000:ℝ)∧Real.exp (49779/100000:ℝ)≤(164509/100000:ℝ)) ∧
((136853/100000:ℝ)≤Real.exp (15687/50000:ℝ)∧Real.exp (15687/50000:ℝ)≤(68427/50000:ℝ)) ∧
((53637/20000:ℝ)≤Real.exp (98651/100000:ℝ)∧Real.exp (98651/100000:ℝ)≤(134093/50000:ℝ)) ∧
((252053/100000:ℝ)≤Real.exp (92447/100000:ℝ)∧Real.exp (92447/100000:ℝ)≤(126027/50000:ℝ)) ∧
((152063/100000:ℝ)≤Real.exp (41913/100000:ℝ)∧Real.exp (41913/100000:ℝ)≤(4752/3125:ℝ)) ∧
((164769/100000:ℝ)≤Real.exp (24969/50000:ℝ)∧Real.exp (24969/50000:ℝ)≤(16477/10000:ℝ)) ∧
((135911/50000:ℝ)≤Real.exp (49999/50000:ℝ)∧Real.exp (49999/50000:ℝ)≤(271823/100000:ℝ)) ∧
((100101/100000:ℝ)≤Real.exp (101/100000:ℝ)∧Real.exp (101/100000:ℝ)≤(50051/50000:ℝ)) ∧
((64201/50000:ℝ)≤Real.exp (1/4:ℝ)∧Real.exp (1/4:ℝ)≤(128403/100000:ℝ)) ∧
((231231/100000:ℝ)≤Real.exp (3353/4000:ℝ)∧Real.exp (3353/4000:ℝ)≤(7226/3125:ℝ)) ∧
((191739/100000:ℝ)≤Real.exp (65097/100000:ℝ)∧Real.exp (65097/100000:ℝ)≤(9587/5000:ℝ)) ∧
((25119/10000:ℝ)≤Real.exp (11513/12500:ℝ)∧Real.exp (11513/12500:ℝ)≤(251191/100000:ℝ)) ∧
((3268/3125:ℝ)≤Real.exp (179/4000:ℝ)∧Real.exp (179/4000:ℝ)≤(104577/100000:ℝ)) ∧
((24301/20000:ℝ)≤Real.exp (19479/100000:ℝ)∧Real.exp (19479/100000:ℝ)≤(60753/50000:ℝ)) ∧
((59977/50000:ℝ)≤Real.exp (9097/50000:ℝ)∧Real.exp (9097/50000:ℝ)≤(23991/20000:ℝ)) ∧
((27789/25000:ℝ)≤Real.exp (10577/100000:ℝ)∧Real.exp (10577/100000:ℝ)≤(111157/100000:ℝ)) ∧
((58389/50000:ℝ)≤Real.exp (15511/100000:ℝ)∧Real.exp (15511/100000:ℝ)≤(116779/100000:ℝ)) ∧
((158203/100000:ℝ)≤Real.exp (45871/100000:ℝ)∧Real.exp (45871/100000:ℝ)≤(39551/25000:ℝ)) ∧
((5721/3125:ℝ)≤Real.exp (60471/100000:ℝ)∧Real.exp (60471/100000:ℝ)≤(183073/100000:ℝ)) ∧
((24837/10000:ℝ)≤Real.exp (3639/4000:ℝ)∧Real.exp (3639/4000:ℝ)≤(248371/100000:ℝ)) ∧
((127101/50000:ℝ)≤Real.exp (5831/6250:ℝ)∧Real.exp (5831/6250:ℝ)≤(254203/100000:ℝ)) ∧
((31217/25000:ℝ)≤Real.exp (22209/100000:ℝ)∧Real.exp (22209/100000:ℝ)≤(124869/100000:ℝ)) ∧
((84893/50000:ℝ)≤Real.exp (52937/100000:ℝ)∧Real.exp (52937/100000:ℝ)≤(169787/100000:ℝ)) ∧
((103777/100000:ℝ)≤Real.exp (927/25000:ℝ)∧Real.exp (927/25000:ℝ)≤(51889/50000:ℝ)) ∧
((62217/50000:ℝ)≤Real.exp (21861/100000:ℝ)∧Real.exp (21861/100000:ℝ)≤(24887/20000:ℝ)) ∧
((51271/25000:ℝ)≤Real.exp (2873/4000:ℝ)∧Real.exp (2873/4000:ℝ)≤(41017/20000:ℝ)) ∧
((50001/50000:ℝ)≤Real.exp (1/50000:ℝ)∧Real.exp (1/50000:ℝ)≤(100003/100000:ℝ)) ∧
((3294/3125:ℝ)≤Real.exp (5267/100000:ℝ)∧Real.exp (5267/100000:ℝ)≤(105409/100000:ℝ)) ∧
((12119/10000:ℝ)≤Real.exp (19219/100000:ℝ)∧Real.exp (19219/100000:ℝ)≤(121191/100000:ℝ)) ∧
((22557/20000:ℝ)≤Real.exp (376/3125:ℝ)∧Real.exp (376/3125:ℝ)≤(56393/50000:ℝ)) ∧
((96897/50000:ℝ)≤Real.exp (66163/100000:ℝ)∧Real.exp (66163/100000:ℝ)≤(38759/20000:ℝ)) ∧
((100001/100000:ℝ)≤Real.exp (2703/250000000:ℝ)∧Real.exp (2703/250000000:ℝ)≤(50001/50000:ℝ)) ∧
((53113/50000:ℝ)≤Real.exp (7551/125000:ℝ)∧Real.exp (7551/125000:ℝ)≤(106227/100000:ℝ)) ∧
((1:ℝ)≤Real.exp (4267/625000000:ℝ)∧Real.exp (4267/625000000:ℝ)≤(100001/100000:ℝ)) ∧
((50003/50000:ℝ)≤Real.exp (15053/250000000:ℝ)∧Real.exp (15053/250000000:ℝ)≤(100007/100000:ℝ)) ∧
((23381/20000:ℝ)≤Real.exp (781/5000:ℝ)∧Real.exp (781/5000:ℝ)≤(58453/50000:ℝ)) ∧
((3132/3125:ℝ)≤Real.exp (22407/10000000:ℝ)∧Real.exp (22407/10000000:ℝ)≤(4009/4000:ℝ)) ∧
((50003/50000:ℝ)≤Real.exp (1383/20000000:ℝ)∧Real.exp (1383/20000000:ℝ)≤(100007/100000:ℝ)) ∧
((31639/20000:ℝ)≤Real.exp (22933/50000:ℝ)∧Real.exp (22933/50000:ℝ)≤(39549/25000:ℝ)) ∧
((119647/100000:ℝ)≤Real.exp (8969/50000:ℝ)∧Real.exp (8969/50000:ℝ)≤(3739/3125:ℝ)) ∧
((107317/100000:ℝ)≤Real.exp (3531/50000:ℝ)∧Real.exp (3531/50000:ℝ)≤(53659/50000:ℝ)) ∧
((36117/25000:ℝ)≤Real.exp (36789/100000:ℝ)∧Real.exp (36789/100000:ℝ)≤(144469/100000:ℝ)) ∧
((100001/100000:ℝ)≤Real.exp (5399/500000000:ℝ)∧Real.exp (5399/500000000:ℝ)≤(50001/50000:ℝ)) ∧
((105913/100000:ℝ)≤Real.exp (57457/1000000:ℝ)∧Real.exp (57457/1000000:ℝ)≤(52957/50000:ℝ)) := by
 exact ⟨EmlComplexity.ExpBoundsProof_unit.p2,⟨EmlComplexity.ExpBoundsProof_unit.p5,⟨EmlComplexity.ExpBoundsProof_unit.p9,⟨EmlComplexity.ExpBoundsProof_unit.p10,⟨EmlComplexity.ExpBoundsProof_unit.p11,⟨EmlComplexity.ExpBoundsProof_unit.p18,⟨EmlComplexity.ExpBoundsProof_unit.p21,⟨EmlComplexity.ExpBoundsProof_unit.p24,⟨EmlComplexity.ExpBoundsProof_unit.p30,⟨EmlComplexity.ExpBoundsProof_unit.p40,⟨EmlComplexity.ExpBoundsProof_unit.p43,⟨EmlComplexity.ExpBoundsProof_unit.p44,⟨EmlComplexity.ExpBoundsProof_unit.p50,⟨EmlComplexity.ExpBoundsProof_unit.p51,⟨EmlComplexity.ExpBoundsProof_unit.p52,⟨EmlComplexity.ExpBoundsProof_unit.p53,⟨EmlComplexity.ExpBoundsProof_unit.p54,⟨EmlComplexity.ExpBoundsProof_unit.p55,⟨EmlComplexity.ExpBoundsProof_unit.p60,⟨EmlComplexity.ExpBoundsProof_unit.p68,⟨EmlComplexity.ExpBoundsProof_unit.p70,⟨EmlComplexity.ExpBoundsProof_unit.p76,⟨EmlComplexity.ExpBoundsProof_unit.p88,⟨EmlComplexity.ExpBoundsProof_unit.p95,⟨EmlComplexity.ExpBoundsProof_unit.p101,⟨EmlComplexity.ExpBoundsProof_unit.p102,⟨EmlComplexity.ExpBoundsProof_unit.p103,⟨EmlComplexity.ExpBoundsProof_unit.p106,⟨EmlComplexity.ExpBoundsProof_unit.p115,⟨EmlComplexity.ExpBoundsProof_unit.p117,⟨EmlComplexity.ExpBoundsProof_unit.p120,⟨EmlComplexity.ExpBoundsProof_unit.p122,⟨EmlComplexity.ExpBoundsProof_unit.p124,⟨EmlComplexity.ExpBoundsProof_unit.p125,⟨EmlComplexity.ExpBoundsProof_unit.p127,⟨EmlComplexity.ExpBoundsProof_unit.p128,⟨EmlComplexity.ExpBoundsProof_unit.p129,⟨EmlComplexity.ExpBoundsProof_unit.p130,⟨EmlComplexity.ExpBoundsProof_unit.p134,⟨EmlComplexity.ExpBoundsProof_unit.p137,⟨EmlComplexity.ExpBoundsProof_unit.p138,⟨EmlComplexity.ExpBoundsProof_unit.p139,⟨EmlComplexity.ExpBoundsProof_unit.p140,⟨EmlComplexity.ExpBoundsProof_unit.p146,⟨EmlComplexity.ExpBoundsProof_unit.p147,⟨EmlComplexity.ExpBoundsProof_unit.p150,⟨EmlComplexity.ExpBoundsProof_unit.p151,⟨EmlComplexity.ExpBoundsProof_unit.p165,⟨EmlComplexity.ExpBoundsProof_unit.p167,⟨EmlComplexity.ExpBoundsProof_unit.p169,⟨EmlComplexity.ExpBoundsProof_unit.p181,⟨EmlComplexity.ExpBoundsProof_unit.p182,⟨EmlComplexity.ExpBoundsProof_unit.p183,⟨EmlComplexity.ExpBoundsProof_unit.p185,⟨EmlComplexity.ExpBoundsProof_unit.p186,⟨EmlComplexity.ExpBoundsProof_unit.p199,⟨EmlComplexity.ExpBoundsProof_unit.p215,⟨EmlComplexity.ExpBoundsProof_unit.p223,⟨EmlComplexity.ExpBoundsProof_unit.p226,⟨EmlComplexity.ExpBoundsProof_unit.p235,⟨EmlComplexity.ExpBoundsProof_unit.p243,⟨EmlComplexity.ExpBoundsProof_unit.p245,⟨EmlComplexity.ExpBoundsProof_unit.p246,⟨EmlComplexity.ExpBoundsProof_unit.p247,⟨EmlComplexity.ExpBoundsProof_unit.p248,⟨EmlComplexity.ExpBoundsProof_unit.p249,⟨EmlComplexity.ExpBoundsProof_unit.p253,⟨EmlComplexity.ExpBoundsProof_unit.p254,⟨EmlComplexity.ExpBoundsProof_unit.p256,⟨EmlComplexity.ExpBoundsProof_unit.p274,⟨EmlComplexity.ExpBoundsProof_unit.p277,⟨EmlComplexity.ExpBoundsProof_unit.p281,⟨EmlComplexity.ExpBoundsProof_unit.p282,⟨EmlComplexity.ExpBoundsProof_unit.p284,⟨EmlComplexity.ExpBoundsProof_unit.p288,⟨EmlComplexity.ExpBoundsProof_unit.p291,⟨EmlComplexity.ExpBoundsProof_unit.p293,⟨EmlComplexity.ExpBoundsProof_unit.p295,⟨EmlComplexity.ExpBoundsProof_unit.p297,⟨EmlComplexity.ExpBoundsProof_unit.p298,⟨EmlComplexity.ExpBoundsProof_unit.p299,⟨EmlComplexity.ExpBoundsProof_unit.p301,⟨EmlComplexity.ExpBoundsProof_unit.p302,⟨EmlComplexity.ExpBoundsProof_unit.p303,⟨EmlComplexity.ExpBoundsProof_unit.p304,⟨EmlComplexity.ExpBoundsProof_unit.p305,⟨EmlComplexity.ExpBoundsProof_unit.p307,⟨EmlComplexity.ExpBoundsProof_unit.p308,⟨EmlComplexity.ExpBoundsProof_unit.p310,⟨EmlComplexity.ExpBoundsProof_unit.p311,⟨EmlComplexity.ExpBoundsProof_unit.p314,EmlComplexity.ExpBoundsProof_unit.p317⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
#print axioms solution
