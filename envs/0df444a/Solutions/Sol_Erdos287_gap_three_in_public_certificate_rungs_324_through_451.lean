-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_324_through_451
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T22:57:14.842817+00:00
-- url     : https://prove2.me/submissions/86d767d0-0688-40d3-9f88-608a66741f8b

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

private def certificateRungs : List Rung :=
  [ ⟨101110291, 919, 2, 24, 3, 3⟩,
    ⟨125753921, 922, 0, 6, 3, 2⟩,
    ⟨77075447, 922, 2, 24, 3, 3⟩,
    ⟨95271217, 925, 0, 6, 3, 2⟩,
    ⟨117054089, 926, 0, 6, 3, 2⟩,
    ⟨73149581, 926, 2, 24, 3, 3⟩,
    ⟨91344871, 927, 2, 24, 3, 3⟩,
    ⟨112518431, 930, 0, 6, 3, 2⟩,
    ⟨67466129, 932, 0, 6, 3, 2⟩,
    ⟨79460581, 931, 2, 24, 3, 3⟩,
    ⟨97269959, 934, 0, 6, 3, 2⟩,
    ⟨117674197, 935, 0, 6, 3, 2⟩,
    ⟨72541081, 935, 2, 24, 3, 3⟩,
    ⟨87469001, 938, 0, 6, 3, 2⟩,
    ⟨108312679, 937, 2, 24, 3, 3⟩,
    ⟨66169891, 939, 2, 24, 3, 3⟩,
    ⟨81092369, 940, 2, 24, 3, 3⟩,
    ⟨100906219, 941, 2, 24, 3, 3⟩,
    ⟨125609027, 942, 2, 24, 3, 3⟩,
    ⟨77481851, 946, 0, 6, 3, 2⟩,
    ⟨94274959, 945, 2, 24, 3, 3⟩,
    ⟨117585431, 948, 0, 6, 3, 2⟩,
    ⟨73322201, 950, 0, 6, 3, 2⟩,
    ⟨88478977, 951, 0, 6, 3, 2⟩,
    ⟨109342157, 950, 2, 24, 3, 3⟩,
    ⟨67774151, 954, 0, 6, 3, 2⟩,
    ⟨83447167, 955, 0, 6, 3, 2⟩,
    ⟨100868219, 956, 0, 6, 3, 2⟩,
    ⟨125718781, 955, 2, 24, 3, 3⟩,
    ⟨75057343, 959, 0, 6, 3, 2⟩,
    ⟨89683637, 958, 2, 24, 3, 3⟩,
    ⟨111627181, 959, 2, 24, 3, 3⟩,
    ⟨69615583, 963, 0, 6, 3, 2⟩,
    ⟨86474051, 964, 0, 6, 3, 2⟩,
    ⟨108031723, 963, 2, 24, 3, 3⟩,
    ⟨65194699, 965, 2, 24, 3, 3⟩,
    ⟨80202557, 966, 2, 24, 3, 3⟩,
    ⟨98771143, 967, 2, 24, 3, 3⟩,
    ⟨122076809, 968, 2, 24, 3, 3⟩,
    ⟨76017269, 972, 0, 6, 3, 2⟩,
    ⟨93760633, 971, 2, 24, 3, 3⟩,
    ⟨116002241, 974, 0, 6, 3, 2⟩,
    ⟨72198521, 974, 2, 24, 3, 3⟩,
    ⟨88800463, 977, 0, 6, 3, 2⟩,
    ⟨109828529, 976, 2, 24, 3, 3⟩,
    ⟨67527401, 980, 0, 6, 3, 2⟩,
    ⟨83888767, 981, 0, 6, 3, 2⟩,
    ⟨104640119, 982, 0, 6, 3, 2⟩,
    ⟨127296517, 981, 2, 24, 3, 3⟩,
    ⟨77268613, 985, 0, 6, 3, 2⟩,
    ⟨93989309, 986, 0, 6, 3, 2⟩,
    ⟨116475043, 987, 0, 6, 3, 2⟩,
    ⟨69957133, 987, 2, 24, 3, 3⟩,
    ⟨83969549, 988, 2, 24, 3, 3⟩,
    ⟨102880177, 989, 2, 24, 3, 3⟩,
    ⟨127612409, 992, 0, 6, 3, 2⟩,
    ⟨79752479, 994, 0, 6, 3, 2⟩,
    ⟨98740987, 993, 2, 24, 3, 3⟩,
    ⟨122960339, 996, 0, 6, 3, 2⟩,
    ⟨76615061, 998, 0, 6, 3, 2⟩,
    ⟨95175397, 999, 0, 6, 3, 2⟩,
    ⟨115521209, 1000, 0, 6, 3, 2⟩,
    ⟨70906019, 1002, 0, 6, 3, 2⟩,
    ⟨87953629, 1001, 2, 24, 3, 3⟩,
    ⟨108841301, 1002, 2, 24, 3, 3⟩,
    ⟨65599433, 1004, 2, 24, 3, 3⟩,
    ⟨80945197, 1005, 2, 24, 3, 3⟩,
    ⟨100447367, 1006, 2, 24, 3, 3⟩,
    ⟨124560103, 1009, 0, 6, 3, 2⟩,
    ⟨71771233, 1011, 0, 6, 3, 2⟩,
    ⟨88777511, 1010, 2, 24, 3, 3⟩,
    ⟨110382421, 1011, 2, 24, 3, 3⟩,
    ⟨68561263, 1015, 0, 6, 3, 2⟩,
    ⟨84578231, 1016, 0, 6, 3, 2⟩,
    ⟨102620893, 1017, 0, 6, 3, 2⟩,
    ⟨127790249, 1018, 0, 6, 3, 2⟩,
    ⟨79487171, 1018, 2, 24, 3, 3⟩,
    ⟨95379103, 1019, 2, 24, 3, 3⟩,
    ⟨118499531, 1022, 0, 6, 3, 2⟩,
    ⟨73145921, 1022, 2, 24, 3, 3⟩,
    ⟨89755123, 1025, 0, 6, 3, 2⟩,
    ⟨109710533, 1024, 2, 24, 3, 3⟩,
    ⟨62713949, 1028, 0, 6, 3, 2⟩,
    ⟨74051581, 1027, 2, 24, 3, 3⟩,
    ⟨91304891, 1030, 0, 6, 3, 2⟩,
    ⟨113857189, 1029, 2, 24, 3, 3⟩,
    ⟨68311231, 1031, 2, 24, 3, 3⟩,
    ⟨84948329, 1034, 0, 6, 3, 2⟩,
    ⟨106129477, 1033, 2, 24, 3, 3⟩,
    ⟨132443669, 1036, 0, 6, 3, 2⟩,
    ⟨81252959, 1036, 2, 24, 3, 3⟩,
    ⟨100941277, 1037, 2, 24, 3, 3⟩,
    ⟨121578791, 1038, 2, 24, 3, 3⟩,
    ⟨75027473, 1040, 2, 24, 3, 3⟩,
    ⟨91607119, 1041, 2, 24, 3, 3⟩,
    ⟨112773989, 1044, 0, 6, 3, 2⟩,
    ⟨69936389, 1046, 0, 6, 3, 2⟩,
    ⟨85078417, 1047, 0, 6, 3, 2⟩,
    ⟨101008601, 1046, 2, 24, 3, 3⟩,
    ⟨125116687, 1049, 0, 6, 3, 2⟩,
    ⟨75086563, 1051, 0, 6, 3, 2⟩,
    ⟨93289271, 1050, 2, 24, 3, 3⟩,
    ⟨116275273, 1053, 0, 6, 3, 2⟩,
    ⟨72330373, 1055, 0, 6, 3, 2⟩,
    ⟨88864799, 1056, 0, 6, 3, 2⟩,
    ⟨110524303, 1057, 0, 6, 3, 2⟩,
    ⟨65332999, 1057, 2, 24, 3, 3⟩,
    ⟨80455511, 1060, 0, 6, 3, 2⟩,
    ⟨99631771, 1059, 2, 24, 3, 3⟩,
    ⟨123511631, 1062, 0, 6, 3, 2⟩,
    ⟨76365881, 1064, 0, 6, 3, 2⟩,
    ⟨93128923, 1065, 0, 6, 3, 2⟩,
    ⟨112807829, 1066, 0, 6, 3, 2⟩,
    ⟨68679857, 1066, 2, 24, 3, 3⟩,
    ⟨84652063, 1069, 0, 6, 3, 2⟩,
    ⟨104891669, 1068, 2, 24, 3, 3⟩,
    ⟨130793989, 1069, 2, 24, 3, 3⟩,
    ⟨80152117, 1073, 0, 6, 3, 2⟩,
    ⟨99391991, 1074, 0, 6, 3, 2⟩,
    ⟨121999177, 1075, 0, 6, 3, 2⟩,
    ⟨74966623, 1077, 0, 6, 3, 2⟩,
    ⟨90075761, 1078, 0, 6, 3, 2⟩,
    ⟨110612857, 1079, 0, 6, 3, 2⟩,
    ⟨67210153, 1081, 0, 6, 3, 2⟩,
    ⟨83893499, 1080, 2, 24, 3, 3⟩,
    ⟨104443567, 1083, 0, 6, 3, 2⟩,
    ⟨129199121, 1082, 2, 24, 3, 3⟩,
    ⟨75861209, 1084, 2, 24, 3, 3⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 7208116319200367450407115533588980011400784121272241099449580028658628209152193060371635799711480110024882516743560588651098146444954442114294176237768388665061338446562753736262843608661830460545436394411515307479615712118070190680809270944500958312921705785003119324582869277805117435 628919486063281440635202976521062403432595061354388928363545825841263440810338906996674850311983730757157126470214095283143956934526967504054074111537354822267076891450829805233739745763600448812851418520291971663867976874379044805453494265712731085943499445304764813311688769692043498937107096292386569754873653176648150890472810741770 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 7208116319200367450407115533588980011400784121272241099449580028658628209152193060371635799711480110024882516743560588651098146444954442114294176237768388665061338446562753736262843608661830460545436394411515307479615712118070190680809270944500958312921705785003119324582869277805117435 < f (k - 1))
    (hhi : f (k - 1) ≤ 628919486063281440635202976521062403432595061354388928363545825841263440810338906996674850311983730757157126470214095283143956934526967504054074111537354822267076891450829805233739745763600448812851418520291971663867976874379044805453494265712731085943499445304764813311688769692043498937107096292386569754873653176648150890472810741770) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

