-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_452_through_579
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T22:58:13.522453+00:00
-- url     : https://prove2.me/submissions/f1f6d823-e2f1-409b-8265-c557f4280e02

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
  [ ⟨93424753, 1087, 0, 6, 3, 2⟩,
    ⟨116473631, 1086, 2, 24, 3, 3⟩,
    ⟨70082063, 1088, 2, 24, 3, 3⟩,
    ⟨83639029, 1089, 2, 24, 3, 3⟩,
    ⟨104373569, 1092, 0, 6, 3, 2⟩,
    ⟨127702381, 1091, 2, 24, 3, 3⟩,
    ⟨78475357, 1095, 0, 6, 3, 2⟩,
    ⟨97546481, 1094, 2, 24, 3, 3⟩,
    ⟨121745731, 1095, 2, 24, 3, 3⟩,
    ⟨75232543, 1099, 0, 6, 3, 2⟩,
    ⟨91436801, 1098, 2, 24, 3, 3⟩,
    ⟨109905277, 1101, 0, 6, 3, 2⟩,
    ⟨64076497, 1101, 2, 24, 3, 3⟩,
    ⟨79029239, 1104, 0, 6, 3, 2⟩,
    ⟨97398121, 1103, 2, 24, 3, 3⟩,
    ⟨120540239, 1104, 2, 24, 3, 3⟩,
    ⟨67461347, 1106, 2, 24, 3, 3⟩,
    ⟨82470781, 1107, 2, 24, 3, 3⟩,
    ⟨102933401, 1110, 0, 6, 3, 2⟩,
    ⟨128555953, 1111, 0, 6, 3, 2⟩,
    ⟨79892257, 1113, 0, 6, 3, 2⟩,
    ⟨99093989, 1112, 2, 24, 3, 3⟩,
    ⟨123800917, 1113, 2, 24, 3, 3⟩,
    ⟨76064977, 1117, 0, 6, 3, 2⟩,
    ⟨93740123, 1116, 2, 24, 3, 3⟩,
    ⟨114091867, 1117, 2, 24, 3, 3⟩,
    ⟨65959027, 1121, 0, 6, 3, 2⟩,
    ⟨81182471, 1122, 0, 6, 3, 2⟩,
    ⟨101422777, 1123, 0, 6, 3, 2⟩,
    ⟨123672371, 1124, 0, 6, 3, 2⟩,
    ⟨75849899, 1126, 0, 6, 3, 2⟩,
    ⟨93933529, 1125, 2, 24, 3, 3⟩,
    ⟨112181141, 1128, 0, 6, 3, 2⟩,
    ⟨69580421, 1130, 0, 6, 3, 2⟩,
    ⟨83311687, 1129, 2, 24, 3, 3⟩,
    ⟨104035031, 1132, 0, 6, 3, 2⟩,
    ⟨125831833, 1131, 2, 24, 3, 3⟩,
    ⟨78003307, 1133, 2, 24, 3, 3⟩,
    ⟨96184541, 1136, 0, 6, 3, 2⟩,
    ⟨114480253, 1137, 0, 6, 3, 2⟩,
    ⟨71173957, 1139, 0, 6, 3, 2⟩,
    ⟨88398221, 1140, 0, 6, 3, 2⟩,
    ⟨107506303, 1141, 0, 6, 3, 2⟩,
    ⟨62682019, 1141, 2, 24, 3, 3⟩,
    ⟨78197591, 1144, 0, 6, 3, 2⟩,
    ⟨96440467, 1145, 0, 6, 3, 2⟩,
    ⟨118843349, 1146, 0, 6, 3, 2⟩,
    ⟨70910627, 1146, 2, 24, 3, 3⟩,
    ⟨88365307, 1149, 0, 6, 3, 2⟩,
    ⟨106281779, 1148, 2, 24, 3, 3⟩,
    ⟨129310627, 1151, 0, 6, 3, 2⟩,
    ⟨80338591, 1151, 2, 24, 3, 3⟩,
    ⟨99257813, 1152, 2, 24, 3, 3⟩,
    ⟨120213367, 1153, 2, 24, 3, 3⟩,
    ⟨74667883, 1157, 0, 6, 3, 2⟩,
    ⟨90294329, 1156, 2, 24, 3, 3⟩,
    ⟨109881043, 1159, 0, 6, 3, 2⟩,
    ⟨63879583, 1161, 0, 6, 3, 2⟩,
    ⟨77185751, 1162, 0, 6, 3, 2⟩,
    ⟨91823467, 1163, 0, 6, 3, 2⟩,
    ⟨113664731, 1164, 0, 6, 3, 2⟩,
    ⟨67644281, 1166, 0, 6, 3, 2⟩,
    ⟨82911007, 1165, 2, 24, 3, 3⟩,
    ⟨103017119, 1168, 0, 6, 3, 2⟩,
    ⟨125794411, 1167, 2, 24, 3, 3⟩,
    ⟨76506433, 1171, 0, 6, 3, 2⟩,
    ⟨94559081, 1172, 0, 6, 3, 2⟩,
    ⟨117443101, 1171, 2, 24, 3, 3⟩,
    ⟨71490193, 1175, 0, 6, 3, 2⟩,
    ⟨87549911, 1174, 2, 24, 3, 3⟩,
    ⟨108232741, 1175, 2, 24, 3, 3⟩,
    ⟨67148023, 1179, 0, 6, 3, 2⟩,
    ⟨79033061, 1178, 2, 24, 3, 3⟩,
    ⟨90818407, 1181, 0, 6, 3, 2⟩,
    ⟨112606199, 1180, 2, 24, 3, 3⟩,
    ⟨67635587, 1182, 2, 24, 3, 3⟩,
    ⟨76600393, 1183, 2, 24, 3, 3⟩,
    ⟨94959119, 1186, 0, 6, 3, 2⟩,
    ⟨115319923, 1187, 0, 6, 3, 2⟩,
    ⟨69433633, 1187, 2, 24, 3, 3⟩,
    ⟨85612889, 1190, 0, 6, 3, 2⟩,
    ⟨104624557, 1189, 2, 24, 3, 3⟩,
    ⟨130599071, 1192, 0, 6, 3, 2⟩,
    ⟨75834023, 1192, 2, 24, 3, 3⟩,
    ⟨89913883, 1195, 0, 6, 3, 2⟩,
    ⟨108652541, 1196, 0, 6, 3, 2⟩,
    ⟨66995699, 1198, 0, 6, 3, 2⟩,
    ⟨83482207, 1199, 0, 6, 3, 2⟩,
    ⟨101296511, 1198, 2, 24, 3, 3⟩,
    ⟨126529651, 1199, 2, 24, 3, 3⟩,
    ⟨77516539, 1201, 2, 24, 3, 3⟩,
    ⟨96716117, 1202, 2, 24, 3, 3⟩,
    ⟨117149887, 1205, 0, 6, 3, 2⟩,
    ⟨72404083, 1207, 0, 6, 3, 2⟩,
    ⟨89454941, 1206, 2, 24, 3, 3⟩,
    ⟨109284193, 1209, 0, 6, 3, 2⟩,
    ⟨65888047, 1211, 0, 6, 3, 2⟩,
    ⟨82246847, 1210, 2, 24, 3, 3⟩,
    ⟨100887277, 1213, 0, 6, 3, 2⟩,
    ⟨123937889, 1214, 0, 6, 3, 2⟩,
    ⟨77341427, 1214, 2, 24, 3, 3⟩,
    ⟨96070297, 1217, 0, 6, 3, 2⟩,
    ⟨115976681, 1218, 0, 6, 3, 2⟩,
    ⟨72332747, 1218, 2, 24, 3, 3⟩,
    ⟨80026393, 1219, 2, 24, 3, 3⟩,
    ⟨98782361, 1222, 0, 6, 3, 2⟩,
    ⟨121603597, 1223, 0, 6, 3, 2⟩,
    ⟨73919311, 1223, 2, 24, 3, 3⟩,
    ⟨92313659, 1226, 0, 6, 3, 2⟩,
    ⟨113728117, 1227, 0, 6, 3, 2⟩,
    ⟨68816533, 1227, 2, 24, 3, 3⟩,
    ⟨84391253, 1228, 2, 24, 3, 3⟩,
    ⟨103377553, 1231, 0, 6, 3, 2⟩,
    ⟨125906999, 1232, 0, 6, 3, 2⟩,
    ⟨78354053, 1232, 2, 24, 3, 3⟩,
    ⟨95277253, 1235, 0, 6, 3, 2⟩,
    ⟨114076961, 1236, 0, 6, 3, 2⟩,
    ⟨70692353, 1236, 2, 24, 3, 3⟩,
    ⟨87076987, 1237, 2, 24, 3, 3⟩,
    ⟨108649529, 1240, 0, 6, 3, 2⟩,
    ⟨67316363, 1240, 2, 24, 3, 3⟩,
    ⟨80027377, 1243, 0, 6, 3, 2⟩,
    ⟨99799109, 1244, 0, 6, 3, 2⟩,
    ⟨120347407, 1245, 0, 6, 3, 2⟩,
    ⟨71349637, 1245, 2, 24, 3, 3⟩,
    ⟨81606191, 1248, 0, 6, 3, 2⟩,
    ⟨98964391, 1247, 2, 24, 3, 3⟩,
    ⟨122797193, 1248, 2, 24, 3, 3⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 628919486063281440635202976521062403432595061354388928363545825841263440810338906996674850311983730757157126470214095283143956934526967504054074111537354822267076891450829805233739745763600448812851418520291971663867976874379044805453494265712731085943499445304764813311688769692043498937107096292386569754873653176648150890472810741770 23805813089741725182015384511104054621492462436169819393247337376348590232433101934819416759323635460150661347734096238203216931254112393534809041441592068475628301049051124656934967823564632980768629149462335397517232454001292587002419225988306705758498861462117908174471405321846075615650603757483916563126131761186680416886434814622774540866409197191052369809358145986408103616184330 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 628919486063281440635202976521062403432595061354388928363545825841263440810338906996674850311983730757157126470214095283143956934526967504054074111537354822267076891450829805233739745763600448812851418520291971663867976874379044805453494265712731085943499445304764813311688769692043498937107096292386569754873653176648150890472810741770 < f (k - 1))
    (hhi : f (k - 1) ≤ 23805813089741725182015384511104054621492462436169819393247337376348590232433101934819416759323635460150661347734096238203216931254112393534809041441592068475628301049051124656934967823564632980768629149462335397517232454001292587002419225988306705758498861462117908174471405321846075615650603757483916563126131761186680416886434814622774540866409197191052369809358145986408103616184330) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

