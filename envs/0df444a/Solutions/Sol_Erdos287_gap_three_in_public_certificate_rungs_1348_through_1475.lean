-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_1348_through_1475
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:22:04.90852+00:00
-- url     : https://prove2.me/submissions/6a1a5138-6d87-4049-ac43-c6db3720c2a2

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

private def squarePowMod (a m : ℕ) : ℕ → ℕ
  | 0 => a % m
  | t + 1 => let residue := squarePowMod a m t; (residue * residue) % m

private theorem squarePowMod_eq (a m t : ℕ) : squarePowMod a m t = a ^ (2 ^ t) % m := by
  induction t with
  | zero => simp [squarePowMod]
  | succ t ih =>
      rw [squarePowMod, ih, ← Nat.mul_mod, pow_succ, pow_mul, pow_two]

private def shiftedPowMod (a m e t : ℕ) : ℕ := squarePowMod (powMod a m e) m t

private theorem shiftedPowMod_eq (a m e t : ℕ) :
    shiftedPowMod a m e t = a ^ (e * 2 ^ t) % m := by
  rw [shiftedPowMod, squarePowMod_eq, powMod_eq, pow_mul]
  exact (Nat.pow_mod (a ^ e) (2 ^ t) m).symm

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

private def Rung.companionPow (r : Rung) : ℕ :=
  squarePowMod (shiftedPowMod r.secondWitness r.q r.oddPart (r.exponent + 1) *
    r.secondWitness % r.q) r.q r.shift

private theorem Rung.companionPow_eq (r : Rung) :
    r.companionPow = powMod r.secondWitness r.q (r.p * 2 ^ r.shift) := by
  rw [Rung.companionPow, squarePowMod_eq, shiftedPowMod_eq, Nat.mod_mul_mod,
    ← pow_succ, powMod_eq, pow_mul]
  exact (Nat.pow_mod (r.secondWitness ^ r.p) (2 ^ r.shift) r.q).symm

/-- Check that this interval extends the interval ending at the given endpoint. -/
def Rung.check (r : Rung) (last : ℕ) : Bool := decide (
  0 < r.oddPart ∧ r.oddPart < 2 ^ (r.exponent + 1) ∧
  shiftedPowMod r.firstWitness r.p r.oddPart r.exponent = r.p - 1 ∧
  r.companionPow = r.q - 1 ∧
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
  rw [shiftedPowMod_eq, ← powMod_eq] at hpw
  rw [Rung.companionPow_eq] at hqw
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
  shiftedPowMod r.leftWitness r.left r.oddPart (r.exponent + 1) = r.left - 1 ∧
  shiftedPowMod r.rightWitness r.right r.oddPart r.exponent = r.right - 1 ∧
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
  rw [shiftedPowMod_eq, ← powMod_eq] at hlw hrw
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
  [ ⟨71812427, 2226, 2, 24, 3, 3⟩,
    ⟨83544553, 2227, 2, 24, 3, 3⟩,
    ⟨100172663, 2228, 2, 24, 3, 3⟩,
    ⟨123215629, 2229, 2, 24, 3, 3⟩,
    ⟨76653721, 2231, 2, 24, 3, 3⟩,
    ⟨90778019, 2234, 0, 6, 3, 2⟩,
    ⟨111078277, 2231, 4, 96, 3, 3⟩,
    ⟨53802493, 2233, 4, 96, 3, 3⟩,
    ⟨65580299, 2236, 2, 24, 3, 3⟩,
    ⟨79321087, 2235, 4, 96, 3, 3⟩,
    ⟨81761261, 2240, 0, 6, 3, 2⟩,
    ⟨99676231, 2239, 2, 24, 3, 3⟩,
    ⟨119579909, 2242, 0, 6, 3, 2⟩,
    ⟨64551761, 2240, 4, 96, 3, 3⟩,
    ⟨79120861, 2243, 2, 24, 3, 3⟩,
    ⟨95808899, 2244, 2, 24, 3, 3⟩,
    ⟨117783097, 2243, 4, 96, 3, 3⟩,
    ⟨72650923, 2245, 4, 96, 3, 3⟩,
    ⟨68039003, 2248, 2, 24, 3, 3⟩,
    ⟨83059729, 2249, 2, 24, 3, 3⟩,
    ⟨99557141, 2252, 0, 6, 3, 2⟩,
    ⟨123215377, 2253, 0, 6, 3, 2⟩,
    ⟨74589967, 2255, 0, 6, 3, 2⟩,
    ⟨92620637, 2254, 2, 24, 3, 3⟩,
    ⟨115424233, 2257, 0, 6, 3, 2⟩,
    ⟨54498187, 2259, 0, 6, 3, 2⟩,
    ⟨50205671, 2256, 4, 96, 3, 3⟩,
    ⟨116289821, 2256, 4, 96, 3, 3⟩,
    ⟨66530549, 2258, 4, 96, 3, 3⟩,
    ⟨83050057, 2259, 4, 96, 3, 3⟩,
    ⟨101538461, 2264, 0, 6, 3, 2⟩,
    ⟨121030051, 2263, 2, 24, 3, 3⟩,
    ⟨75393187, 2263, 4, 96, 3, 3⟩,
    ⟨91622159, 2268, 0, 6, 3, 2⟩,
    ⟨108929113, 2265, 4, 96, 3, 3⟩,
    ⟨65987917, 2267, 4, 96, 3, 3⟩,
    ⟨81436631, 2270, 2, 24, 3, 3⟩,
    ⟨99955651, 2271, 2, 24, 3, 3⟩,
    ⟨124042493, 2272, 2, 24, 3, 3⟩,
    ⟨74321279, 2272, 4, 96, 3, 3⟩,
    ⟨92744983, 2277, 0, 6, 3, 2⟩,
    ⟨114293783, 2276, 2, 24, 3, 3⟩,
    ⟨66140771, 2280, 0, 6, 3, 2⟩,
    ⟨69189061, 2279, 2, 24, 3, 3⟩,
    ⟨83477039, 2278, 4, 96, 3, 3⟩,
    ⟨102937543, 2279, 4, 96, 3, 3⟩,
    ⟨125239997, 2282, 2, 24, 3, 3⟩,
    ⟨76782833, 2284, 2, 24, 3, 3⟩,
    ⟨93353107, 2287, 0, 6, 3, 2⟩,
    ⟨115949711, 2284, 4, 96, 3, 3⟩,
    ⟨64948991, 2290, 0, 6, 3, 2⟩,
    ⟨72152653, 2287, 4, 96, 3, 3⟩,
    ⟨80794451, 2288, 4, 96, 3, 3⟩,
    ⟨99362113, 2291, 2, 24, 3, 3⟩,
    ⟨121921799, 2290, 4, 96, 3, 3⟩,
    ⟨73916651, 2292, 4, 96, 3, 3⟩,
    ⟨84607573, 2297, 0, 6, 3, 2⟩,
    ⟨102121139, 2296, 2, 24, 3, 3⟩,
    ⟨114189139, 2297, 2, 24, 3, 3⟩,
    ⟨70735111, 2299, 2, 24, 3, 3⟩,
    ⟨85113929, 2298, 4, 96, 3, 3⟩,
    ⟨98277559, 2301, 2, 24, 3, 3⟩,
    ⟨120518591, 2304, 0, 6, 3, 2⟩,
    ⟨74983199, 2306, 0, 6, 3, 2⟩,
    ⟨92108377, 2305, 2, 24, 3, 3⟩,
    ⟨114642131, 2308, 0, 6, 3, 2⟩,
    ⟨70368059, 2308, 2, 24, 3, 3⟩,
    ⟨79742749, 2309, 2, 24, 3, 3⟩,
    ⟨92933741, 2312, 0, 6, 3, 2⟩,
    ⟨115258477, 2309, 4, 96, 3, 3⟩,
    ⟨63793759, 2313, 2, 24, 3, 3⟩,
    ⟨75358001, 2316, 0, 6, 3, 2⟩,
    ⟨89383351, 2315, 2, 24, 3, 3⟩,
    ⟨96285731, 2318, 0, 6, 3, 2⟩,
    ⟨106240873, 2319, 0, 6, 3, 2⟩,
    ⟨131644169, 2320, 0, 6, 3, 2⟩,
    ⟨76456889, 2322, 0, 6, 3, 2⟩,
    ⟨94760383, 2319, 4, 96, 3, 3⟩,
    ⟨117522227, 2322, 2, 24, 3, 3⟩,
    ⟨71112401, 2326, 0, 6, 3, 2⟩,
    ⟨86604277, 2327, 0, 6, 3, 2⟩,
    ⟨99460979, 2328, 0, 6, 3, 2⟩,
    ⟨104332357, 2329, 0, 6, 3, 2⟩,
    ⟨116485709, 2330, 0, 6, 3, 2⟩,
    ⟨72367511, 2332, 0, 6, 3, 2⟩,
    ⟨81468847, 2333, 0, 6, 3, 2⟩,
    ⟨97836551, 2330, 4, 96, 3, 3⟩,
    ⟨118533097, 2331, 4, 96, 3, 3⟩,
    ⟨60363841, 2335, 2, 24, 3, 3⟩,
    ⟨61539389, 2338, 0, 6, 3, 2⟩,
    ⟨71245753, 2339, 0, 6, 3, 2⟩,
    ⟨84527477, 2338, 2, 24, 3, 3⟩,
    ⟨91585177, 2337, 4, 96, 3, 3⟩,
    ⟨112476443, 2340, 2, 24, 3, 3⟩,
    ⟨61077011, 2344, 0, 6, 3, 2⟩,
    ⟨76074793, 2341, 4, 96, 3, 3⟩,
    ⟨93718619, 2344, 2, 24, 3, 3⟩,
    ⟨116368453, 2343, 4, 96, 3, 3⟩,
    ⟨67721893, 2345, 4, 96, 3, 3⟩,
    ⟨75559613, 2348, 2, 24, 3, 3⟩,
    ⟨87252523, 2351, 0, 6, 3, 2⟩,
    ⟨98912267, 2350, 2, 24, 3, 3⟩,
    ⟨122495743, 2349, 4, 96, 3, 3⟩,
    ⟨72887047, 2355, 0, 6, 3, 2⟩,
    ⟨90441119, 2352, 4, 96, 3, 3⟩,
    ⟨99582823, 2357, 0, 6, 3, 2⟩,
    ⟨114863381, 2354, 4, 96, 3, 3⟩,
    ⟨66058871, 2358, 2, 24, 3, 3⟩,
    ⟨82109323, 2361, 0, 6, 3, 2⟩,
    ⟨99645701, 2362, 0, 6, 3, 2⟩,
    ⟨123519073, 2359, 4, 96, 3, 3⟩,
    ⟨68033143, 2365, 0, 6, 3, 2⟩,
    ⟨70949741, 2362, 4, 96, 3, 3⟩,
    ⟨85462987, 2365, 2, 24, 3, 3⟩,
    ⟨102643691, 2366, 2, 24, 3, 3⟩,
    ⟨127212703, 2367, 2, 24, 3, 3⟩,
    ⟨77271289, 2369, 2, 24, 3, 3⟩,
    ⟨93383951, 2372, 0, 6, 3, 2⟩,
    ⟨115319131, 2371, 2, 24, 3, 3⟩,
    ⟨64424719, 2373, 2, 24, 3, 3⟩,
    ⟨78984701, 2376, 0, 6, 3, 2⟩,
    ⟨88394323, 2377, 0, 6, 3, 2⟩,
    ⟨101444723, 2376, 2, 24, 3, 3⟩,
    ⟨118620727, 2375, 4, 96, 3, 3⟩,
    ⟨73682767, 2377, 4, 96, 3, 3⟩,
    ⟨81220259, 2380, 2, 24, 3, 3⟩,
    ⟨100452697, 2383, 0, 6, 3, 2⟩,
    ⟨114736211, 2380, 4, 96, 3, 3⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 14917400282768037724101041560968701267360400256242255035809474064707246528412288917092516333985090352260728920591046337154370609379528030949121105929822816886696857118760011428854175343085474356238795672322794518348632894664774032659860217332998397533048770384954063046191426862623782138063046100471004704479210742005525655163942090131681951262461054196857026922473670806973126571861995046349333568272765925697859170545194466691078979821699353619497612947435554265872706699419577094759503032664747966982659738982169889708538941767695124927117424970813106256373591672021392966759334881865184644745270574984482739485207249869124123810945159873003785631940699756132103451743470223370 5190511609513286114787594527988091920162924362008625326039055882884689345831184141393879706181319002521499809866844456796623602507288503136397953131584251948051512094510404678371402944102141029425830466039509451228295656704162223215834461954296096504659464323581599754700290793863907204375548508012665508156143800085085155589119387923961215552905460611543758173717241232079065502153815087898086790880083066781163650199495717232430496135714721682697571995046400561109729099261691577993188703825985508850660360622662690363881110079909218863241973421171011139285845125583153757743884403345223371187810149059484239311233228270501582551053242175211733557261768908929697659148705849880151484706879223702950381468944540397993732341830 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 14917400282768037724101041560968701267360400256242255035809474064707246528412288917092516333985090352260728920591046337154370609379528030949121105929822816886696857118760011428854175343085474356238795672322794518348632894664774032659860217332998397533048770384954063046191426862623782138063046100471004704479210742005525655163942090131681951262461054196857026922473670806973126571861995046349333568272765925697859170545194466691078979821699353619497612947435554265872706699419577094759503032664747966982659738982169889708538941767695124927117424970813106256373591672021392966759334881865184644745270574984482739485207249869124123810945159873003785631940699756132103451743470223370 < f (k - 1))
    (hhi : f (k - 1) ≤ 5190511609513286114787594527988091920162924362008625326039055882884689345831184141393879706181319002521499809866844456796623602507288503136397953131584251948051512094510404678371402944102141029425830466039509451228295656704162223215834461954296096504659464323581599754700290793863907204375548508012665508156143800085085155589119387923961215552905460611543758173717241232079065502153815087898086790880083066781163650199495717232430496135714721682697571995046400561109729099261691577993188703825985508850660360622662690363881110079909218863241973421171011139285845125583153757743884403345223371187810149059484239311233228270501582551053242175211733557261768908929697659148705849880151484706879223702950381468944540397993732341830) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

