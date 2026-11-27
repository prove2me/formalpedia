-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_836_through_963
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:01:55.820021+00:00
-- url     : https://prove2.me/submissions/da2433a7-163f-4af6-8ed8-4f31401794fa

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
  [ ⟨82144837, 1581, 0, 6, 3, 2⟩,
    ⟨101105189, 1582, 0, 6, 3, 2⟩,
    ⟨125410897, 1579, 4, 96, 3, 3⟩,
    ⟨77625193, 1583, 2, 24, 3, 3⟩,
    ⟨94732433, 1584, 2, 24, 3, 3⟩,
    ⟨116234497, 1583, 4, 96, 3, 3⟩,
    ⟨72529867, 1585, 4, 96, 3, 3⟩,
    ⟨89205923, 1588, 2, 24, 3, 3⟩,
    ⟨110507707, 1589, 2, 24, 3, 3⟩,
    ⟨66381397, 1593, 0, 6, 3, 2⟩,
    ⟨82280249, 1592, 2, 24, 3, 3⟩,
    ⟨102345517, 1595, 0, 6, 3, 2⟩,
    ⟨120137987, 1594, 2, 24, 3, 3⟩,
    ⟨74659001, 1594, 4, 96, 3, 3⟩,
    ⟨92793709, 1597, 2, 24, 3, 3⟩,
    ⟨115294061, 1598, 2, 24, 3, 3⟩,
    ⟨69116549, 1602, 0, 6, 3, 2⟩,
    ⟨81479617, 1603, 0, 6, 3, 2⟩,
    ⟨97925369, 1600, 4, 96, 3, 3⟩,
    ⟨116765647, 1601, 4, 96, 3, 3⟩,
    ⟨70620727, 1603, 4, 96, 3, 3⟩,
    ⟨87841241, 1604, 4, 96, 3, 3⟩,
    ⟨107270011, 1607, 2, 24, 3, 3⟩,
    ⟨129630779, 1608, 2, 24, 3, 3⟩,
    ⟨80576261, 1612, 0, 6, 3, 2⟩,
    ⟨93463351, 1611, 2, 24, 3, 3⟩,
    ⟨116492549, 1610, 4, 96, 3, 3⟩,
    ⟨72019061, 1614, 2, 24, 3, 3⟩,
    ⟨89050153, 1613, 4, 96, 3, 3⟩,
    ⟨108608261, 1618, 0, 6, 3, 2⟩,
    ⟨67330811, 1616, 4, 96, 3, 3⟩,
    ⟨82709197, 1617, 4, 96, 3, 3⟩,
    ⟨103215683, 1620, 2, 24, 3, 3⟩,
    ⟨127913683, 1623, 0, 6, 3, 2⟩,
    ⟨74453293, 1625, 0, 6, 3, 2⟩,
    ⟨90499361, 1622, 4, 96, 3, 3⟩,
    ⟨111312067, 1627, 0, 6, 3, 2⟩,
    ⟨68076553, 1629, 0, 6, 3, 2⟩,
    ⟨81187919, 1628, 2, 24, 3, 3⟩,
    ⟨99517603, 1631, 0, 6, 3, 2⟩,
    ⟨120686921, 1632, 0, 6, 3, 2⟩,
    ⟨75366311, 1630, 4, 96, 3, 3⟩,
    ⟨92514067, 1633, 2, 24, 3, 3⟩,
    ⟨115617077, 1634, 2, 24, 3, 3⟩,
    ⟨70719791, 1634, 4, 96, 3, 3⟩,
    ⟨81464923, 1639, 0, 6, 3, 2⟩,
    ⟨101736281, 1636, 4, 96, 3, 3⟩,
    ⟨124194757, 1637, 4, 96, 3, 3⟩,
    ⟨75623773, 1643, 0, 6, 3, 2⟩,
    ⟨92583317, 1642, 2, 24, 3, 3⟩,
    ⟨109122751, 1643, 2, 24, 3, 3⟩,
    ⟨67656187, 1645, 2, 24, 3, 3⟩,
    ⟨83914517, 1646, 2, 24, 3, 3⟩,
    ⟨103765813, 1645, 4, 96, 3, 3⟩,
    ⟨126038513, 1648, 2, 24, 3, 3⟩,
    ⟨77034899, 1648, 4, 96, 3, 3⟩,
    ⟨94248853, 1653, 0, 6, 3, 2⟩,
    ⟨116639069, 1654, 0, 6, 3, 2⟩,
    ⟨72190091, 1654, 2, 24, 3, 3⟩,
    ⟨82889197, 1657, 0, 6, 3, 2⟩,
    ⟨102315581, 1658, 0, 6, 3, 2⟩,
    ⟨120247999, 1657, 2, 24, 3, 3⟩,
    ⟨72802783, 1659, 2, 24, 3, 3⟩,
    ⟨88610261, 1662, 0, 6, 3, 2⟩,
    ⟨110617483, 1659, 4, 96, 3, 3⟩,
    ⟨67407817, 1661, 4, 96, 3, 3⟩,
    ⟨84110513, 1664, 2, 24, 3, 3⟩,
    ⟨102897937, 1665, 2, 24, 3, 3⟩,
    ⟨126718511, 1664, 4, 96, 3, 3⟩,
    ⟨77105201, 1670, 0, 6, 3, 2⟩,
    ⟨95249563, 1667, 4, 96, 3, 3⟩,
    ⟨118182851, 1670, 2, 24, 3, 3⟩,
    ⟨73490981, 1674, 0, 6, 3, 2⟩,
    ⟨91225507, 1675, 0, 6, 3, 2⟩,
    ⟨108222761, 1672, 4, 96, 3, 3⟩,
    ⟨66833381, 1674, 4, 96, 3, 3⟩,
    ⟨82527337, 1675, 4, 96, 3, 3⟩,
    ⟨99626711, 1678, 2, 24, 3, 3⟩,
    ⟨123310933, 1677, 4, 96, 3, 3⟩,
    ⟨75498889, 1681, 2, 24, 3, 3⟩,
    ⟨89798171, 1680, 4, 96, 3, 3⟩,
    ⟨102086227, 1685, 0, 6, 3, 2⟩,
    ⟨126212789, 1682, 4, 96, 3, 3⟩,
    ⟨74163731, 1686, 2, 24, 3, 3⟩,
    ⟨91499893, 1685, 4, 96, 3, 3⟩,
    ⟨113048981, 1690, 0, 6, 3, 2⟩,
    ⟨69490919, 1688, 4, 96, 3, 3⟩,
    ⟨86304007, 1693, 0, 6, 3, 2⟩,
    ⟨99100283, 1692, 2, 24, 3, 3⟩,
    ⟨113607997, 1693, 2, 24, 3, 3⟩,
    ⟨70305133, 1693, 4, 96, 3, 3⟩,
    ⟨82102829, 1696, 2, 24, 3, 3⟩,
    ⟨91264807, 1695, 4, 96, 3, 3⟩,
    ⟨102944657, 1698, 2, 24, 3, 3⟩,
    ⟨119425213, 1697, 4, 96, 3, 3⟩,
    ⟨70974457, 1703, 0, 6, 3, 2⟩,
    ⟨86909741, 1700, 4, 96, 3, 3⟩,
    ⟨103522591, 1703, 2, 24, 3, 3⟩,
    ⟨125977289, 1704, 2, 24, 3, 3⟩,
    ⟨76910891, 1704, 4, 96, 3, 3⟩,
    ⟨96045667, 1709, 0, 6, 3, 2⟩,
    ⟨116642069, 1706, 4, 96, 3, 3⟩,
    ⟨70490351, 1712, 0, 6, 3, 2⟩,
    ⟨84136567, 1713, 0, 6, 3, 2⟩,
    ⟨102085679, 1714, 0, 6, 3, 2⟩,
    ⟨121994107, 1715, 0, 6, 3, 2⟩,
    ⟨75364633, 1717, 0, 6, 3, 2⟩,
    ⟨86643281, 1718, 0, 6, 3, 2⟩,
    ⟨105476587, 1719, 0, 6, 3, 2⟩,
    ⟨130340531, 1716, 4, 96, 3, 3⟩,
    ⟨80222399, 1718, 4, 96, 3, 3⟩,
    ⟨98274097, 1719, 4, 96, 3, 3⟩,
    ⟨122051411, 1720, 4, 96, 3, 3⟩,
    ⟨73723229, 1726, 0, 6, 3, 2⟩,
    ⟨89376277, 1725, 2, 24, 3, 3⟩,
    ⟨104563127, 1726, 2, 24, 3, 3⟩,
    ⟨126951163, 1727, 2, 24, 3, 3⟩,
    ⟨75889657, 1729, 2, 24, 3, 3⟩,
    ⟨92447489, 1732, 0, 6, 3, 2⟩,
    ⟨102384973, 1733, 0, 6, 3, 2⟩,
    ⟨124456001, 1730, 4, 96, 3, 3⟩,
    ⟨74962931, 1734, 2, 24, 3, 3⟩,
    ⟨92817601, 1735, 2, 24, 3, 3⟩,
    ⟨115047773, 1736, 2, 24, 3, 3⟩,
    ⟨70232621, 1738, 2, 24, 3, 3⟩,
    ⟨85717843, 1737, 4, 96, 3, 3⟩,
    ⟨105375989, 1740, 2, 24, 3, 3⟩,
    ⟨128453323, 1743, 0, 6, 3, 2⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 29428619997427176983703258157449149865729626198280850041789871181683230008706424694203145482741988123923176318024260498707379817567630588566055418950300618889488063018356885335479953088222333634323199968693949681460058480756671503744829144927342817866436458777557396529649644007753790531845684979672707127956552559711673544855451004522913764879108752230061444274931337291324364429354134845182525250902246831392579266812055309766984156409476298209798380790526919093467394277278859919355 636836264107884224170981213922020606776871637335787800494260876707575901779301126473150287798281603227628312525625618385353763358302881457937963895588641442433332672557746265798686262058801146826205970685315315997755021351141406643135235290580248208125204643829947256311797521244895290596637340576105551317024592076326205647751850947191424061251762297349475663145357548008768858945602327989878966238401172184816403513211553384277179564271866716409652435035837230493238762860996136287867681823837449237363416857214095383222103666851835 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 29428619997427176983703258157449149865729626198280850041789871181683230008706424694203145482741988123923176318024260498707379817567630588566055418950300618889488063018356885335479953088222333634323199968693949681460058480756671503744829144927342817866436458777557396529649644007753790531845684979672707127956552559711673544855451004522913764879108752230061444274931337291324364429354134845182525250902246831392579266812055309766984156409476298209798380790526919093467394277278859919355 < f (k - 1))
    (hhi : f (k - 1) ≤ 636836264107884224170981213922020606776871637335787800494260876707575901779301126473150287798281603227628312525625618385353763358302881457937963895588641442433332672557746265798686262058801146826205970685315315997755021351141406643135235290580248208125204643829947256311797521244895290596637340576105551317024592076326205647751850947191424061251762297349475663145357548008768858945602327989878966238401172184816403513211553384277179564271866716409652435035837230493238762860996136287867681823837449237363416857214095383222103666851835) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

