-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_1604_through_1731
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:20:57.222983+00:00
-- url     : https://prove2.me/submissions/ad1c0101-3dff-4427-926f-7a8f6ab1e5a8

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
  [ ⟨103090093, 2539, 2, 24, 3, 3⟩,
    ⟨126985031, 2538, 4, 96, 3, 3⟩,
    ⟨69130601, 2542, 2, 24, 3, 3⟩,
    ⟨77914597, 2541, 4, 96, 3, 3⟩,
    ⟨79857611, 2546, 0, 6, 3, 2⟩,
    ⟨89694133, 2547, 0, 6, 3, 2⟩,
    ⟨100849919, 2548, 0, 6, 3, 2⟩,
    ⟨123786373, 2549, 0, 6, 3, 2⟩,
    ⟨63934657, 2549, 2, 24, 3, 3⟩,
    ⟨79838201, 2550, 2, 24, 3, 3⟩,
    ⟨77114473, 2549, 4, 96, 3, 3⟩,
    ⟨96372359, 2554, 0, 6, 3, 2⟩,
    ⟨118359187, 2551, 4, 96, 3, 3⟩,
    ⟨70444483, 2555, 2, 24, 3, 3⟩,
    ⟨87886241, 2554, 4, 96, 3, 3⟩,
    ⟨101035147, 2555, 4, 96, 3, 3⟩,
    ⟨125606291, 2556, 4, 96, 3, 3⟩,
    ⟨71284439, 2560, 2, 24, 3, 3⟩,
    ⟨86805337, 2561, 2, 24, 3, 3⟩,
    ⟨108490709, 2564, 0, 6, 3, 2⟩,
    ⟨56811113, 2564, 2, 24, 3, 3⟩,
    ⟨70868167, 2563, 4, 96, 3, 3⟩,
    ⟨87996287, 2566, 2, 24, 3, 3⟩,
    ⟨101257843, 2565, 4, 96, 3, 3⟩,
    ⟨120177209, 2570, 0, 6, 3, 2⟩,
    ⟨72706631, 2568, 4, 96, 3, 3⟩,
    ⟨78982723, 2571, 2, 24, 3, 3⟩,
    ⟨96532379, 2574, 0, 6, 3, 2⟩,
    ⟨115048357, 2571, 4, 96, 3, 3⟩,
    ⟨57199573, 2577, 0, 6, 3, 2⟩,
    ⟨57349319, 2574, 4, 96, 3, 3⟩,
    ⟨44246977, 2577, 2, 24, 3, 3⟩,
    ⟨110479147, 2577, 2, 24, 3, 3⟩,
    ⟨54855727, 2581, 0, 6, 3, 2⟩,
    ⟨67037699, 2582, 0, 6, 3, 2⟩,
    ⟨82020919, 2581, 2, 24, 3, 3⟩,
    ⟨101477951, 2580, 4, 96, 3, 3⟩,
    ⟨125247127, 2585, 0, 6, 3, 2⟩,
    ⟨77656387, 2583, 4, 96, 3, 3⟩,
    ⟨96152747, 2586, 2, 24, 3, 3⟩,
    ⟨115367023, 2585, 4, 96, 3, 3⟩,
    ⟨60901597, 2589, 2, 24, 3, 3⟩,
    ⟨68208599, 2592, 0, 6, 3, 2⟩,
    ⟨77479177, 2593, 0, 6, 3, 2⟩,
    ⟨83369423, 2592, 2, 24, 3, 3⟩,
    ⟨81680353, 2595, 0, 6, 3, 2⟩,
    ⟨102066131, 2596, 0, 6, 3, 2⟩,
    ⟨124873663, 2597, 0, 6, 3, 2⟩,
    ⟨76623577, 2599, 0, 6, 3, 2⟩,
    ⟨83463431, 2598, 2, 24, 3, 3⟩,
    ⟨96969511, 2599, 2, 24, 3, 3⟩,
    ⟨114928241, 2602, 0, 6, 3, 2⟩,
    ⟨71567141, 2600, 4, 96, 3, 3⟩,
    ⟨83748883, 2603, 2, 24, 3, 3⟩,
    ⟨97573841, 2606, 0, 6, 3, 2⟩,
    ⟨105417517, 2605, 2, 24, 3, 3⟩,
    ⟨107285231, 2604, 4, 96, 3, 3⟩,
    ⟨130768423, 2605, 4, 96, 3, 3⟩,
    ⟨73735657, 2609, 2, 24, 3, 3⟩,
    ⟨87780827, 2610, 2, 24, 3, 3⟩,
    ⟨107514907, 2609, 4, 96, 3, 3⟩,
    ⟨52427887, 2613, 2, 24, 3, 3⟩,
    ⟨127724413, 2615, 0, 6, 3, 2⟩,
    ⟨68231677, 2617, 0, 6, 3, 2⟩,
    ⟨78423503, 2616, 2, 24, 3, 3⟩,
    ⟨97998403, 2619, 0, 6, 3, 2⟩,
    ⟨101206121, 2618, 2, 24, 3, 3⟩,
    ⟨87311743, 2621, 0, 6, 3, 2⟩,
    ⟨100878863, 2620, 2, 24, 3, 3⟩,
    ⟨123649507, 2621, 2, 24, 3, 3⟩,
    ⟨72846073, 2625, 0, 6, 3, 2⟩,
    ⟨90032291, 2622, 4, 96, 3, 3⟩,
    ⟨100701943, 2623, 4, 96, 3, 3⟩,
    ⟨123613121, 2626, 2, 24, 3, 3⟩,
    ⟨71900111, 2626, 4, 96, 3, 3⟩,
    ⟨88043233, 2631, 0, 6, 3, 2⟩,
    ⟨104890031, 2630, 2, 24, 3, 3⟩,
    ⟨129150517, 2629, 4, 96, 3, 3⟩,
    ⟨78449383, 2631, 4, 96, 3, 3⟩,
    ⟨89451359, 2632, 4, 96, 3, 3⟩,
    ⟨89495647, 2633, 4, 96, 3, 3⟩,
    ⟨111822629, 2638, 0, 6, 3, 2⟩,
    ⟨61713629, 2636, 4, 96, 3, 3⟩,
    ⟨74233891, 2639, 2, 24, 3, 3⟩,
    ⟨91373369, 2638, 4, 96, 3, 3⟩,
    ⟨109418563, 2639, 4, 96, 3, 3⟩,
    ⟨65717173, 2645, 0, 6, 3, 2⟩,
    ⟨81865871, 2642, 4, 96, 3, 3⟩,
    ⟨95053393, 2647, 0, 6, 3, 2⟩,
    ⟨113222189, 2648, 0, 6, 3, 2⟩,
    ⟨64853501, 2646, 4, 96, 3, 3⟩,
    ⟨80474167, 2651, 0, 6, 3, 2⟩,
    ⟨83028299, 2652, 0, 6, 3, 2⟩,
    ⟨90514033, 2649, 4, 96, 3, 3⟩,
    ⟨112811381, 2650, 4, 96, 3, 3⟩,
    ⟨62939501, 2656, 0, 6, 3, 2⟩,
    ⟨73746307, 2657, 0, 6, 3, 2⟩,
    ⟨90614309, 2658, 0, 6, 3, 2⟩,
    ⟨109945567, 2657, 2, 24, 3, 3⟩,
    ⟨63287977, 2661, 0, 6, 3, 2⟩,
    ⟨75139529, 2660, 2, 24, 3, 3⟩,
    ⟨90413767, 2659, 4, 96, 3, 3⟩,
    ⟨110116031, 2664, 0, 6, 3, 2⟩,
    ⟨65001689, 2662, 4, 96, 3, 3⟩,
    ⟨76630117, 2667, 0, 6, 3, 2⟩,
    ⟨94507541, 2668, 0, 6, 3, 2⟩,
    ⟨117969877, 2665, 4, 96, 3, 3⟩,
    ⟨66801289, 2669, 2, 24, 3, 3⟩,
    ⟨70271309, 2672, 0, 6, 3, 2⟩,
    ⟨85791757, 2673, 0, 6, 3, 2⟩,
    ⟨90701159, 2674, 0, 6, 3, 2⟩,
    ⟨99418369, 2673, 2, 24, 3, 3⟩,
    ⟨123634391, 2676, 0, 6, 3, 2⟩,
    ⟨74166149, 2678, 0, 6, 3, 2⟩,
    ⟨68838727, 2679, 0, 6, 3, 2⟩,
    ⟨71284529, 2680, 0, 6, 3, 2⟩,
    ⟨80085583, 2681, 0, 6, 3, 2⟩,
    ⟨60425639, 2680, 2, 24, 3, 3⟩,
    ⟨70650163, 2683, 0, 6, 3, 2⟩,
    ⟨88027781, 2680, 4, 96, 3, 3⟩,
    ⟨104663353, 2683, 2, 24, 3, 3⟩,
    ⟨117691181, 2682, 4, 96, 3, 3⟩,
    ⟨64445699, 2684, 4, 96, 3, 3⟩,
    ⟨78636013, 2685, 4, 96, 3, 3⟩,
    ⟨84013883, 2688, 2, 24, 3, 3⟩,
    ⟨100664287, 2687, 4, 96, 3, 3⟩,
    ⟨120866261, 2688, 4, 96, 3, 3⟩,
    ⟨72089531, 2690, 4, 96, 3, 3⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 375655950749750963594794050166441859956201305806153200223296666449545613801007696981094494765810988919274217304886085801694056263744933379815907364094713662630092967376779440600840576767538721943443639994165853850846728373471353207775861836229650437268178022037077820853463021438001889637906492381774840813193247212611930006780179533122269922239174796769058806641589523813283927745471735682150681731765740518432482287180063622566916001197659553695041218225807514443536988654011707435475642063623831171862431945978814321969419718643401018847583870870765524988491357684054442877602844439906459147554778522668790432547713506210039625791232279655980588640142449123428562729171249579125738355504095693863753807385999909536811072468327988123435964778521609025665191665221018583035 6802687467857223928666416896072006166970798354323982721730818052242995938973734099166809510086698117810202780424129548904912950420138909605881018637422801565030100590719538116961276870323518837437867788633689332009052293300508848229737910785823708652851099536871351262841686997468404515250992136666895980700019323886852373675062663212276486816565454021209378871960729438522238577067632182496863719363462094415019359356262687234456773233891336837656700621831265193032151704028375831643538616821854926261424080330631916324515234991083524553397244180928409513670544643538845218817608158191830270907960834215547551230702427695275795851175412004515242842358304872581998365710929358669758196573356198703816775019045200732198920975412008396219093076587196845310795373565455029930798310387893491284498734835872772039117939671110 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 375655950749750963594794050166441859956201305806153200223296666449545613801007696981094494765810988919274217304886085801694056263744933379815907364094713662630092967376779440600840576767538721943443639994165853850846728373471353207775861836229650437268178022037077820853463021438001889637906492381774840813193247212611930006780179533122269922239174796769058806641589523813283927745471735682150681731765740518432482287180063622566916001197659553695041218225807514443536988654011707435475642063623831171862431945978814321969419718643401018847583870870765524988491357684054442877602844439906459147554778522668790432547713506210039625791232279655980588640142449123428562729171249579125738355504095693863753807385999909536811072468327988123435964778521609025665191665221018583035 < f (k - 1))
    (hhi : f (k - 1) ≤ 6802687467857223928666416896072006166970798354323982721730818052242995938973734099166809510086698117810202780424129548904912950420138909605881018637422801565030100590719538116961276870323518837437867788633689332009052293300508848229737910785823708652851099536871351262841686997468404515250992136666895980700019323886852373675062663212276486816565454021209378871960729438522238577067632182496863719363462094415019359356262687234456773233891336837656700621831265193032151704028375831643538616821854926261424080330631916324515234991083524553397244180928409513670544643538845218817608158191830270907960834215547551230702427695275795851175412004515242842358304872581998365710929358669758196573356198703816775019045200732198920975412008396219093076587196845310795373565455029930798310387893491284498734835872772039117939671110) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

