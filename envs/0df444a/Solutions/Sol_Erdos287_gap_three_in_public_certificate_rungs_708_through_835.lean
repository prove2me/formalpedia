-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_708_through_835
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:00:54.441853+00:00
-- url     : https://prove2.me/submissions/b504bab2-05d2-4bc0-923d-6354adf912c3

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
  [ ⟨68478457, 1413, 4, 96, 3, 3⟩,
    ⟨84820751, 1418, 0, 6, 3, 2⟩,
    ⟨104823889, 1417, 2, 24, 3, 3⟩,
    ⟨128637737, 1418, 2, 24, 3, 3⟩,
    ⟨79541879, 1420, 2, 24, 3, 3⟩,
    ⟨97751107, 1419, 4, 96, 3, 3⟩,
    ⟨121376777, 1422, 2, 24, 3, 3⟩,
    ⟨74987639, 1422, 4, 96, 3, 3⟩,
    ⟨93731887, 1423, 4, 96, 3, 3⟩,
    ⟨110317379, 1428, 0, 6, 3, 2⟩,
    ⟨66266609, 1426, 4, 96, 3, 3⟩,
    ⟨81772543, 1431, 0, 6, 3, 2⟩,
    ⟨101447681, 1432, 0, 6, 3, 2⟩,
    ⟨123218713, 1431, 2, 24, 3, 3⟩,
    ⟨74638093, 1431, 4, 96, 3, 3⟩,
    ⟨92959871, 1434, 2, 24, 3, 3⟩,
    ⟨115302571, 1435, 2, 24, 3, 3⟩,
    ⟨71836399, 1437, 2, 24, 3, 3⟩,
    ⟨89280959, 1436, 4, 96, 3, 3⟩,
    ⟨111594433, 1441, 0, 6, 3, 2⟩,
    ⟨66492649, 1441, 2, 24, 3, 3⟩,
    ⟨78546089, 1444, 0, 6, 3, 2⟩,
    ⟨95594797, 1441, 4, 96, 3, 3⟩,
    ⟨118580039, 1446, 0, 6, 3, 2⟩,
    ⟨71562461, 1448, 0, 6, 3, 2⟩,
    ⟨85233013, 1449, 0, 6, 3, 2⟩,
    ⟨105570791, 1446, 4, 96, 3, 3⟩,
    ⟨129014569, 1449, 2, 24, 3, 3⟩,
    ⟨76611193, 1451, 2, 24, 3, 3⟩,
    ⟨94529933, 1452, 2, 24, 3, 3⟩,
    ⟨116661763, 1451, 4, 96, 3, 3⟩,
    ⟨70758697, 1453, 4, 96, 3, 3⟩,
    ⟨87958823, 1456, 2, 24, 3, 3⟩,
    ⟨109143607, 1459, 0, 6, 3, 2⟩,
    ⟨68042683, 1457, 4, 96, 3, 3⟩,
    ⟨84211619, 1460, 2, 24, 3, 3⟩,
    ⟨101033437, 1463, 0, 6, 3, 2⟩,
    ⟨125692991, 1462, 2, 24, 3, 3⟩,
    ⟨72794699, 1464, 2, 24, 3, 3⟩,
    ⟨90287803, 1467, 0, 6, 3, 2⟩,
    ⟨112245839, 1464, 4, 96, 3, 3⟩,
    ⟨65187431, 1466, 4, 96, 3, 3⟩,
    ⟨81471883, 1471, 0, 6, 3, 2⟩,
    ⟨98651909, 1468, 4, 96, 3, 3⟩,
    ⟨123055663, 1469, 4, 96, 3, 3⟩,
    ⟨76364647, 1471, 4, 96, 3, 3⟩,
    ⟨94051637, 1474, 2, 24, 3, 3⟩,
    ⟨117424183, 1475, 2, 24, 3, 3⟩,
    ⟨70659397, 1479, 0, 6, 3, 2⟩,
    ⟨85619819, 1476, 4, 96, 3, 3⟩,
    ⟨106205977, 1477, 4, 96, 3, 3⟩,
    ⟨132206339, 1482, 0, 6, 3, 2⟩,
    ⟨81581579, 1480, 4, 96, 3, 3⟩,
    ⟨92701321, 1483, 2, 24, 3, 3⟩,
    ⟨113478851, 1486, 0, 6, 3, 2⟩,
    ⟨68577521, 1488, 0, 6, 3, 2⟩,
    ⟨85104307, 1485, 4, 96, 3, 3⟩,
    ⟨102317939, 1490, 0, 6, 3, 2⟩,
    ⟨127847509, 1489, 2, 24, 3, 3⟩,
    ⟨77892937, 1493, 0, 6, 3, 2⟩,
    ⟨90079151, 1490, 4, 96, 3, 3⟩,
    ⟨110374807, 1491, 4, 96, 3, 3⟩,
    ⟨67019647, 1497, 0, 6, 3, 2⟩,
    ⟨82953869, 1494, 4, 96, 3, 3⟩,
    ⟨96148147, 1495, 4, 96, 3, 3⟩,
    ⟨119800781, 1496, 4, 96, 3, 3⟩,
    ⟨73924391, 1498, 4, 96, 3, 3⟩,
    ⟨90184777, 1501, 2, 24, 3, 3⟩,
    ⟨109234091, 1504, 0, 6, 3, 2⟩,
    ⟨66523469, 1506, 0, 6, 3, 2⟩,
    ⟨82577923, 1503, 4, 96, 3, 3⟩,
    ⟨102053267, 1506, 2, 24, 3, 3⟩,
    ⟨124260757, 1505, 4, 96, 3, 3⟩,
    ⟨77550589, 1509, 2, 24, 3, 3⟩,
    ⟨94711481, 1512, 0, 6, 3, 2⟩,
    ⟨117110557, 1509, 4, 96, 3, 3⟩,
    ⟨71606347, 1513, 2, 24, 3, 3⟩,
    ⟨89506421, 1514, 2, 24, 3, 3⟩,
    ⟨95323687, 1517, 0, 6, 3, 2⟩,
    ⟨113701649, 1514, 4, 96, 3, 3⟩,
    ⟨65443769, 1516, 4, 96, 3, 3⟩,
    ⟨79209313, 1519, 2, 24, 3, 3⟩,
    ⟨98983529, 1518, 4, 96, 3, 3⟩,
    ⟨121678423, 1519, 4, 96, 3, 3⟩,
    ⟨74932747, 1521, 4, 96, 3, 3⟩,
    ⟨90448859, 1526, 0, 6, 3, 2⟩,
    ⟨110368303, 1523, 4, 96, 3, 3⟩,
    ⟨62676091, 1527, 2, 24, 3, 3⟩,
    ⟨72445361, 1526, 4, 96, 3, 3⟩,
    ⟨90210433, 1527, 4, 96, 3, 3⟩,
    ⟨112469411, 1532, 0, 6, 3, 2⟩,
    ⟨69541343, 1532, 2, 24, 3, 3⟩,
    ⟨79211179, 1533, 2, 24, 3, 3⟩,
    ⟨97682159, 1532, 4, 96, 3, 3⟩,
    ⟨121599223, 1533, 4, 96, 3, 3⟩,
    ⟨72804163, 1535, 4, 96, 3, 3⟩,
    ⟨89490581, 1536, 4, 96, 3, 3⟩,
    ⟨108386077, 1537, 4, 96, 3, 3⟩,
    ⟨63280597, 1541, 2, 24, 3, 3⟩,
    ⟨75327557, 1542, 2, 24, 3, 3⟩,
    ⟨91885447, 1541, 4, 96, 3, 3⟩,
    ⟨114489299, 1546, 0, 6, 3, 2⟩,
    ⟨71384609, 1548, 0, 6, 3, 2⟩,
    ⟨85323523, 1545, 4, 96, 3, 3⟩,
    ⟨102295019, 1548, 2, 24, 3, 3⟩,
    ⟨125938807, 1549, 2, 24, 3, 3⟩,
    ⟨76116283, 1553, 0, 6, 3, 2⟩,
    ⟨92112311, 1554, 0, 6, 3, 2⟩,
    ⟨114700477, 1553, 2, 24, 3, 3⟩,
    ⟨70744783, 1557, 0, 6, 3, 2⟩,
    ⟨85379351, 1558, 0, 6, 3, 2⟩,
    ⟨103642633, 1559, 0, 6, 3, 2⟩,
    ⟨122887139, 1560, 0, 6, 3, 2⟩,
    ⟨75674591, 1558, 4, 96, 3, 3⟩,
    ⟨90219907, 1559, 4, 96, 3, 3⟩,
    ⟨110545811, 1560, 4, 96, 3, 3⟩,
    ⟨67573529, 1566, 0, 6, 3, 2⟩,
    ⟨84444319, 1565, 2, 24, 3, 3⟩,
    ⟨102060941, 1568, 0, 6, 3, 2⟩,
    ⟨125970553, 1565, 4, 96, 3, 3⟩,
    ⟨72021637, 1569, 2, 24, 3, 3⟩,
    ⟨89445017, 1570, 2, 24, 3, 3⟩,
    ⟨109787773, 1571, 2, 24, 3, 3⟩,
    ⟨67472617, 1571, 4, 96, 3, 3⟩,
    ⟨83045741, 1576, 0, 6, 3, 2⟩,
    ⟨103254133, 1573, 4, 96, 3, 3⟩,
    ⟨122688689, 1578, 0, 6, 3, 2⟩,
    ⟨69402761, 1580, 0, 6, 3, 2⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 1054969579998128804454027271818151521307676020941187320829926552626863692246372373821807093438564019097076004377751497616232485518668074925157713081582174881186241713185561699949790602314567033785617528217260791029814584138367632078695007565513679136095774321065675238064883928760368607578720172502051098479988773620608017545659485684745884790298940635846153902456198655319272838897781971640414867433422520586100071366783895895843799035 29428619997427176983703258157449149865729626198280850041789871181683230008706424694203145482741988123923176318024260498707379817567630588566055418950300618889488063018356885335479953088222333634323199968693949681460058480756671503744829144927342817866436458777557396529649644007753790531845684979672707127956552559711673544855451004522913764879108752230061444274931337291324364429354134845182525250902246831392579266812055309766984156409476298209798380790526919093467394277278859919355 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 1054969579998128804454027271818151521307676020941187320829926552626863692246372373821807093438564019097076004377751497616232485518668074925157713081582174881186241713185561699949790602314567033785617528217260791029814584138367632078695007565513679136095774321065675238064883928760368607578720172502051098479988773620608017545659485684745884790298940635846153902456198655319272838897781971640414867433422520586100071366783895895843799035 < f (k - 1))
    (hhi : f (k - 1) ≤ 29428619997427176983703258157449149865729626198280850041789871181683230008706424694203145482741988123923176318024260498707379817567630588566055418950300618889488063018356885335479953088222333634323199968693949681460058480756671503744829144927342817866436458777557396529649644007753790531845684979672707127956552559711673544855451004522913764879108752230061444274931337291324364429354134845182525250902246831392579266812055309766984156409476298209798380790526919093467394277278859919355) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

