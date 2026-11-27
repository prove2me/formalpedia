-- Prove2me | solution 1 for Erdos287.gap_three_in_compacted_proth_pair_rungs_13_through_76
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:08:24.601856+00:00
-- url     : https://prove2.me/submissions/643e45f1-a83e-4e24-bdf3-30da650444fe

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Theorems.Thm_Erdos287_proth_prime_certificate
import Theorems.Thm_Erdos287_factorial_prime_rung

open Finset

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Erdos287.CompactRungs

/-- Each step halves the exponent and reduces the intermediate residue. -/
def powModBits (a m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | fuel + 1, e =>
      let x := powModBits a m fuel (e / 2)
      (x * x * (if e % 2 = 0 then 1 else a)) % m

theorem powModBits_eq (a m fuel e : ℕ) (he : e < 2 ^ fuel) :
    powModBits a m fuel e = a ^ e % m := by
  induction fuel generalizing e with
  | zero =>
      have he0 : e = 0 := by simpa using he
      simp [he0, powModBits]
  | succ fuel ih =>
      have hhalf : e / 2 < 2 ^ fuel := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
        simpa only [pow_succ] using he
      have hparity : (if e % 2 = 0 then 1 else a) = a ^ (e % 2) := by
        rcases Nat.mod_two_eq_zero_or_one e with h | h <;> simp [h]
      have hsplit : e = e / 2 + e / 2 + e % 2 := by omega
      rw [powModBits, ih _ hhalf, hparity,
        ← Nat.mod_mul_mod (a ^ (e / 2) % m * (a ^ (e / 2) % m)) (a ^ (e % 2)) m,
        ← Nat.mul_mod (a ^ (e / 2)) (a ^ (e / 2)) m, Nat.mod_mul_mod]
      conv_rhs => rw [hsplit, pow_add, pow_add]

def powMod (a m e : ℕ) : ℕ := powModBits a m (e.log2 + 1) e

theorem powMod_eq (a m e : ℕ) : powMod a m e = a ^ e % m := by
  apply powModBits_eq
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by decide) e

private theorem zmod_powMod (a n e : ℕ) :
    (a : ZMod n) ^ e = (powMod a n e : ZMod n) := by
  rw [powMod_eq, ← Nat.cast_pow]
  exact CharP.natCast_eq_natCast_mod (ZMod n) n (a ^ e)

private theorem cast_pred (n : ℕ) (hn : 0 < n) : ((n - 1 : ℕ) : ZMod n) = -1 := by
  apply eq_neg_of_add_eq_zero_left
  calc
    ((n - 1 : ℕ) : ZMod n) + 1 = ((n - 1 + 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_add, Nat.cast_one]
    _ = 0 := by rw [Nat.sub_add_cancel hn, ZMod.natCast_self]

structure Rung where
  oddPart : ℕ
  exponent : ℕ
  shift : ℕ
  cofactorCap : ℕ
  firstWitness : ℕ
  secondWitness : ℕ

def Rung.p (r : Rung) : ℕ := r.oddPart * 2 ^ (r.exponent + 1) + 1

def Rung.x (r : Rung) : ℕ := r.p * 2 ^ (r.shift + 1)

def Rung.q (r : Rung) : ℕ := r.x + 1

def Rung.upper (r : Rung) : ℕ := (5 * r.x - 20) / 2

/-- Check that this interval extends the interval ending at the given endpoint. -/
def Rung.check (r : Rung) (last : ℕ) : Bool := decide (
  0 < r.oddPart ∧ r.oddPart < 2 ^ (r.exponent + 1) ∧
  powMod r.firstWitness r.p (r.oddPart * 2 ^ r.exponent) = r.p - 1 ∧
  powMod r.secondWitness r.q (r.p * 2 ^ r.shift) = r.q - 1 ∧
  powMod r.secondWitness r.q (2 ^ (r.shift + 1)) ≠ 1 ∧
  r.cofactorCap * r.cofactorCap.factorial < r.p ∧ 4 < r.q ∧
  r.x + 2 ≤ last + 1 ∧ last ≤ r.upper ∧
  r.upper < (r.cofactorCap + 1) * r.p ∧ r.upper < 3 * r.q ∧
  2 * r.upper + 20 ≤ 5 * r.x)

private theorem half_power_eq_neg_one (a n e : ℕ) (hn : 0 < n)
    (h : powMod a n e = n - 1) : (a : ZMod n) ^ e = -1 := by
  rw [zmod_powMod, h, cast_pred n hn]

private theorem second_prime (r : Rung) (hp : r.p.Prime) (hq : 4 < r.q)
    (hh : (r.secondWitness : ZMod r.q) ^ (r.p * 2 ^ r.shift) = -1)
    (hsmall : powMod r.secondWitness r.q (2 ^ (r.shift + 1)) ≠ 1) :
    r.q.Prime := by
  let _ : Fact (1 < r.q) := ⟨by omega⟩
  let _ : NeZero r.q := ⟨by omega⟩
  have hfactor : r.q - 1 = r.p * 2 ^ (r.shift + 1) := by simp [Rung.q, Rung.x]
  have hhalf : r.q - 1 = (r.p * 2 ^ r.shift) * 2 := by
    rw [hfactor, pow_succ, mul_assoc]
  let a : ZMod r.q := r.secondWitness
  have hfull : a ^ (r.q - 1) = 1 := by
    rw [hhalf, pow_mul, show a ^ (r.p * 2 ^ r.shift) = -1 from hh]
    norm_num
  apply lucas_primality r.q a hfull
  intro p hp' hdiv
  rw [hfactor] at hdiv
  rcases hp'.dvd_mul.mp hdiv with h | h
  · have he : p = r.p := (Nat.prime_dvd_prime_iff_eq hp' hp).mp h
    subst p
    rw [hfactor, Nat.mul_comm, Nat.mul_div_cancel _ hp.pos]
    intro heq
    have hvalue := congrArg ZMod.val heq
    have hmod : powMod r.secondWitness r.q (2 ^ (r.shift + 1)) < r.q := by
      rw [powMod_eq]
      exact Nat.mod_lt _ (by omega)
    rw [show a = (r.secondWitness : ZMod r.q) from rfl, zmod_powMod, ZMod.val_natCast,
      Nat.mod_eq_of_lt hmod, ZMod.val_one] at hvalue
    exact hsmall hvalue
  · have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp (hp'.dvd_of_dvd_pow h)
    subst p
    rw [hhalf, Nat.mul_div_cancel _ (by decide : 0 < 2),
      show a ^ (r.p * 2 ^ r.shift) = -1 from hh]
    intro hneg
    have hvalue : ((r.q - 1 : ℕ) : ZMod r.q) = 1 :=
      (cast_pred r.q (by omega)).trans hneg
    have hb := congrArg ZMod.val hvalue
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : r.q - 1 < r.q), ZMod.val_one] at hb
    omega

abbrev HasGap (k : ℕ) (f : ℕ → ℕ) :=
  ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i

theorem rung_gap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (r : Rung) (last : ℕ) (hcheck : r.check last = true)
    (hlast : last < f (k - 1)) (hupper : f (k - 1) ≤ r.upper) :
    HasGap k f := by
  unfold Rung.check at hcheck
  obtain ⟨hodd, hbound, hpw, hqw, hsmall, hfact, hq4, hlo, _, hhip, hhiq, hband⟩ :=
    of_decide_eq_true hcheck
  have hp1 : 0 < r.p := Nat.zero_lt_succ _
  have hp : r.p.Prime := Erdos287.proth_prime_certificate r.oddPart r.exponent
    r.firstWitness hodd hbound (half_power_eq_neg_one _ _ _ hp1 hpw)
  have hq : r.q.Prime := second_prime r hp hq4
    (half_power_eq_neg_one _ _ _ (by omega) hqw) hsmall
  exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum r.x r.p r.q r.cofactorCap 2
    hp hq ⟨2 ^ (r.shift + 1), rfl⟩ (dvd_refl _) hfact (by simpa using hq4)
    (by omega) (hupper.trans_lt hhip) (hupper.trans_lt hhiq) (by omega)

private def checkIntervals {α : Type} (check : α → ℕ → Bool) (upper : α → ℕ) :
    List α → ℕ → ℕ → Bool
  | [], start, finish => decide (start = finish)
  | r :: tail, start, finish => check r start && checkIntervals check upper tail (upper r) finish

private theorem checkedIntervalsGap {α : Type} (k : ℕ) (f : ℕ → ℕ)
    (check : α → ℕ → Bool) (upper : α → ℕ)
    (sound : ∀ r start, check r start = true → start < f (k - 1) →
      f (k - 1) ≤ upper r → HasGap k f)
    (rungs : List α) (start finish : ℕ)
    (hcheck : checkIntervals check upper rungs start finish = true)
    (hlow : start < f (k - 1)) (hhigh : f (k - 1) ≤ finish) :
    HasGap k f := by
  induction rungs generalizing start with
  | nil =>
      have h : start = finish := of_decide_eq_true hcheck
      omega
  | cons r tail ih =>
      obtain ⟨hr, ht⟩ := Bool.and_eq_true_iff.mp hcheck
      by_cases h : f (k - 1) ≤ upper r
      · exact sound r start hr hlow h
      · exact ih (upper r) ht (Nat.lt_of_not_ge h)

def checkChain := checkIntervals Rung.check Rung.upper

theorem chain_gap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (rungs : List Rung) (start finish : ℕ)
    (hcheck : checkChain rungs start finish = true)
    (hlow : start < f (k - 1)) (hhigh : f (k - 1) ≤ finish) :
    HasGap k f :=
  checkedIntervalsGap k f Rung.check Rung.upper
    (rung_gap k hk f hf1 hmono hsum) rungs start finish hcheck hlow hhigh

structure ProthPair where
  oddPart : ℕ
  exponent : ℕ
  leftWitness : ℕ
  rightWitness : ℕ

def ProthPair.left (r : ProthPair) : ℕ := r.oddPart * 2 ^ (r.exponent + 1 + 1) + 1

def ProthPair.right (r : ProthPair) : ℕ := r.oddPart * 2 ^ (r.exponent + 1) + 1

def ProthPair.upper (r : ProthPair) : ℕ := (5 * r.left - 20) / 2

def ProthPair.check (r : ProthPair) (last : ℕ) : Bool := decide (
  0 < r.oddPart ∧ r.oddPart < 2 ^ (r.exponent + 1) ∧
  powMod r.leftWitness r.left (r.oddPart * 2 ^ (r.exponent + 1)) = r.left - 1 ∧
  powMod r.rightWitness r.right (r.oddPart * 2 ^ r.exponent) = r.right - 1 ∧
  4 < r.left ∧ 96 < r.right ∧
  r.left + 2 ≤ last + 1 ∧ last ≤ r.upper ∧
  r.upper < 3 * r.left ∧ r.upper < 5 * r.right ∧
  2 * r.upper + 20 ≤ 5 * r.left)

private theorem proth_pair_gap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (r : ProthPair) (last : ℕ) (hcheck : r.check last = true)
    (hlast : last < f (k - 1)) (hupper : f (k - 1) ≤ r.upper) :
    HasGap k f := by
  unfold ProthPair.check at hcheck
  obtain ⟨hodd, hsmall, hlw, hrw, hl4, hr96, hlo, _, hhip, hhiq, hband⟩ :=
    of_decide_eq_true hcheck
  have hsmallLeft : r.oddPart < 2 ^ (r.exponent + 1 + 1) := by
    rw [pow_succ]
    omega
  have hp : r.left.Prime := Erdos287.proth_prime_certificate r.oddPart (r.exponent + 1)
    r.leftWitness hodd hsmallLeft (half_power_eq_neg_one _ _ _ (by omega) hlw)
  have hq : r.right.Prime := Erdos287.proth_prime_certificate r.oddPart r.exponent
    r.rightWitness hodd hsmall (half_power_eq_neg_one _ _ _ (by omega) hrw)
  have hdouble : r.left + 1 = r.right * 2 := by simp [ProthPair.left, ProthPair.right, pow_succ]; ring
  exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum r.left r.left r.right 2 4
    hp hq (dvd_refl _) ⟨2, hdouble⟩ (by simpa using hl4) (by simpa [Nat.factorial] using hr96)
    (by omega) (hupper.trans_lt hhip) (hupper.trans_lt hhiq) (by omega)

def checkProthChain := checkIntervals ProthPair.check ProthPair.upper

theorem proth_chain_gap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (rungs : List ProthPair) (start finish : ℕ)
    (hcheck : checkProthChain rungs start finish = true)
    (hlow : start < f (k - 1)) (hhigh : f (k - 1) ≤ finish) :
    HasGap k f :=
  checkedIntervalsGap k f ProthPair.check ProthPair.upper
    (proth_pair_gap k hk f hf1 hmono hsum) rungs start finish hcheck hlow hhigh

end Erdos287.CompactRungs

open Erdos287.CompactRungs

private def certificateRungs : List ProthPair :=
  [ ⟨5031716622, 2905, 5, 13⟩,
    ⟨5870622132, 2906, 5, 5⟩,
    ⟨6850923906, 2907, 5, 5⟩,
    ⟨7990356255, 2908, 17, 11⟩,
    ⟨4660959060, 2910, 11, 7⟩,
    ⟨5439017403, 2911, 5, 7⟩,
    ⟨6345556953, 2912, 5, 5⟩,
    ⟨7402897314, 2913, 5, 5⟩,
    ⟨4318388538, 2915, 5, 7⟩,
    ⟨5037758268, 2916, 5, 5⟩,
    ⟨5876675910, 2917, 17, 11⟩,
    ⟨6856078005, 2918, 11, 11⟩,
    ⟨7999039110, 2919, 19, 7⟩,
    ⟨4667953302, 2921, 5, 7⟩,
    ⟨5444908881, 2922, 5, 7⟩,
    ⟨6350998290, 2923, 11, 11⟩,
    ⟨7410068499, 2924, 5, 13⟩,
    ⟨4323241470, 2926, 7, 13⟩,
    ⟨5047718400, 2927, 11, 7⟩,
    ⟨5883482430, 2928, 11, 11⟩,
    ⟨6863776872, 2929, 5, 7⟩,
    ⟨8009057826, 2930, 5, 29⟩,
    ⟨4671035880, 2932, 17, 11⟩,
    ⟨5449414845, 2933, 11, 17⟩,
    ⟨6358230360, 2934, 17, 7⟩,
    ⟨7417254930, 2935, 11, 7⟩,
    ⟨4327009380, 2937, 7, 7⟩,
    ⟨5047909317, 2938, 5, 5⟩,
    ⟨5890150908, 2939, 5, 7⟩,
    ⟨6871327173, 2940, 5, 5⟩,
    ⟨8016481974, 2941, 5, 5⟩,
    ⟨4675888431, 2943, 5, 5⟩,
    ⟨5455182834, 2944, 5, 7⟩,
    ⟨6364812540, 2945, 7, 7⟩,
    ⟨7426518411, 2946, 5, 11⟩,
    ⟨4332559023, 2948, 5, 5⟩,
    ⟨5055407064, 2949, 5, 5⟩,
    ⟨5896781667, 2950, 5, 5⟩,
    ⟨6879434853, 2951, 5, 7⟩,
    ⟨8024193813, 2952, 5, 5⟩,
    ⟨4682762757, 2954, 5, 5⟩,
    ⟨5462648970, 2955, 13, 7⟩,
    ⟨6371430153, 2956, 5, 5⟩,
    ⟨7434482874, 2957, 5, 5⟩,
    ⟨4336962078, 2959, 5, 7⟩,
    ⟨5058581805, 2960, 13, 7⟩,
    ⟨5902053252, 2961, 5, 11⟩,
    ⟨6889172865, 2962, 17, 7⟩,
    ⟨8035746735, 2963, 7, 7⟩,
    ⟨4687579017, 2965, 5, 17⟩,
    ⟨5469335982, 2966, 5, 5⟩,
    ⟨6380048535, 2967, 11, 11⟩,
    ⟨7441145439, 2968, 5, 11⟩,
    ⟨4341159750, 2970, 7, 23⟩,
    ⟨5064305535, 2971, 7, 11⟩,
    ⟨5912920725, 2972, 11, 7⟩,
    ⟨6892693269, 2973, 5, 5⟩,
    ⟨8041854297, 2974, 5, 5⟩,
    ⟨4690759500, 2976, 11, 23⟩,
    ⟨5472965205, 2977, 17, 7⟩,
    ⟨6385588431, 2978, 5, 7⟩,
    ⟨7448965293, 2979, 5, 23⟩,
    ⟨4345521159, 2981, 5, 5⟩,
    ⟨5070413952, 2982, 5, 5⟩ ]

private theorem certificateVerified :
    checkProthChain certificateRungs 669708429961437326974827859966491465278674758363031663260923778702594127142843992769122875022473532305604941070470912086779213001535728934750530688118528455353813769919465134235648785658311691184556782410037084055168384233166908093399119264857403342969972893458590610787872752822883709995274442148971977897472828841697043926285826230330370467309787556575495207597653775009477537270687874728887490412578175120193942507643605458893922940153515791872337587714229370239761772971098173811120316297761345707083057998710656148745326219726799270421878585858738563917209037999133923772751859010058483811176326445574429570488073908651456146128986522851136156620298611423434621866423364515125348587559362299881650179201382529765845618685930182942560331917332460647498246757984924988632452531245154632974458992486116685706522076374147550949004886682742449588735810828871276392214036414928561111032 237952617733822117836785444486503936290182495276806449612599457700039100028115230384352378913592176876934028153847147527271492443946323848057020754857442167451235018928418454782130294372329914828052571354945056440410039861516367734762707615462996988759646163898794903053141636626387975730138701122898645675419328428402609020156404239568458989159286908809980778558487395163532097741381098688355666769001293538516494442631527317281346623725367476077424923737602104283795077845310536780240107535666658474997239340622463182089324766484814627176578066331432774465437785064152596109807499948991300490654728683354797930546019353210306273948507118291525240424596629340075898313269443975300054271865845043067382734414200687397412463460698153552533195771308066125753703202901064843040617271765243648071610747813450160507011251201339215525489531463169476236039234447076140999071616141334793510225034295176114299029422072 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 669708429961437326974827859966491465278674758363031663260923778702594127142843992769122875022473532305604941070470912086779213001535728934750530688118528455353813769919465134235648785658311691184556782410037084055168384233166908093399119264857403342969972893458590610787872752822883709995274442148971977897472828841697043926285826230330370467309787556575495207597653775009477537270687874728887490412578175120193942507643605458893922940153515791872337587714229370239761772971098173811120316297761345707083057998710656148745326219726799270421878585858738563917209037999133923772751859010058483811176326445574429570488073908651456146128986522851136156620298611423434621866423364515125348587559362299881650179201382529765845618685930182942560331917332460647498246757984924988632452531245154632974458992486116685706522076374147550949004886682742449588735810828871276392214036414928561111032 < f (k - 1))
    (hhi : f (k - 1) ≤ 237952617733822117836785444486503936290182495276806449612599457700039100028115230384352378913592176876934028153847147527271492443946323848057020754857442167451235018928418454782130294372329914828052571354945056440410039861516367734762707615462996988759646163898794903053141636626387975730138701122898645675419328428402609020156404239568458989159286908809980778558487395163532097741381098688355666769001293538516494442631527317281346623725367476077424923737602104283795077845310536780240107535666658474997239340622463182089324766484814627176578066331432774465437785064152596109807499948991300490654728683354797930546019353210306273948507118291525240424596629340075898313269443975300054271865845043067382734414200687397412463460698153552533195771308066125753703202901064843040617271765243648071610747813450160507011251201339215525489531463169476236039234447076140999071616141334793510225034295176114299029422072) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact proth_chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

