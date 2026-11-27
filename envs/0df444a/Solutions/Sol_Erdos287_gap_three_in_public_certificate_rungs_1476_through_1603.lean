-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_1476_through_1603
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:20:57.141818+00:00
-- url     : https://prove2.me/submissions/e97073ee-e15c-475f-b4ba-9ca45a719a89

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
  [ ⟨70437869, 2382, 4, 96, 3, 3⟩,
    ⟨82894183, 2387, 0, 6, 3, 2⟩,
    ⟨100683329, 2384, 4, 96, 3, 3⟩,
    ⟨124689127, 2389, 0, 6, 3, 2⟩,
    ⟨76843777, 2387, 4, 96, 3, 3⟩,
    ⟨94030301, 2388, 4, 96, 3, 3⟩,
    ⟨113898823, 2393, 0, 6, 3, 2⟩,
    ⟨68663743, 2395, 0, 6, 3, 2⟩,
    ⟨83399681, 2394, 2, 24, 3, 3⟩,
    ⟨100730053, 2397, 0, 6, 3, 2⟩,
    ⟨109279829, 2394, 4, 96, 3, 3⟩,
    ⟨68236451, 2396, 4, 96, 3, 3⟩,
    ⟨78141241, 2399, 2, 24, 3, 3⟩,
    ⟨97288391, 2402, 0, 6, 3, 2⟩,
    ⟨119761333, 2403, 0, 6, 3, 2⟩,
    ⟨72398437, 2401, 4, 96, 3, 3⟩,
    ⟨90242129, 2402, 4, 96, 3, 3⟩,
    ⟨109877197, 2407, 0, 6, 3, 2⟩,
    ⟨65963533, 2409, 0, 6, 3, 2⟩,
    ⟨66045281, 2406, 4, 96, 3, 3⟩,
    ⟨81949477, 2409, 2, 24, 3, 3⟩,
    ⟨93697937, 2410, 2, 24, 3, 3⟩,
    ⟨87411253, 2409, 4, 96, 3, 3⟩,
    ⟨106873583, 2412, 2, 24, 3, 3⟩,
    ⟨131505043, 2411, 4, 96, 3, 3⟩,
    ⟨77117653, 2417, 0, 6, 3, 2⟩,
    ⟨95129999, 2416, 2, 24, 3, 3⟩,
    ⟨118483087, 2419, 0, 6, 3, 2⟩,
    ⟨68590147, 2417, 4, 96, 3, 3⟩,
    ⟨69722801, 2418, 4, 96, 3, 3⟩,
    ⟨80440993, 2419, 4, 96, 3, 3⟩,
    ⟨93412181, 2424, 0, 6, 3, 2⟩,
    ⟨114405787, 2425, 0, 6, 3, 2⟩,
    ⟨63900523, 2423, 4, 96, 3, 3⟩,
    ⟨71902601, 2428, 0, 6, 3, 2⟩,
    ⟨87161917, 2429, 0, 6, 3, 2⟩,
    ⟨108868139, 2426, 4, 96, 3, 3⟩,
    ⟨66832331, 2428, 4, 96, 3, 3⟩,
    ⟨57473197, 2433, 0, 6, 3, 2⟩,
    ⟨71088209, 2432, 2, 24, 3, 3⟩,
    ⟨73984957, 2431, 4, 96, 3, 3⟩,
    ⟨71580059, 2436, 0, 6, 3, 2⟩,
    ⟨87276121, 2435, 2, 24, 3, 3⟩,
    ⟨108754769, 2434, 4, 96, 3, 3⟩,
    ⟨67034117, 2438, 2, 24, 3, 3⟩,
    ⟨79534633, 2437, 4, 96, 3, 3⟩,
    ⟨96233171, 2442, 0, 6, 3, 2⟩,
    ⟨116069953, 2443, 0, 6, 3, 2⟩,
    ⟨62826877, 2441, 4, 96, 3, 3⟩,
    ⟨78013781, 2442, 4, 96, 3, 3⟩,
    ⟨88532113, 2447, 0, 6, 3, 2⟩,
    ⟨108966029, 2448, 0, 6, 3, 2⟩,
    ⟨65245289, 2448, 2, 24, 3, 3⟩,
    ⟨71708803, 2447, 4, 96, 3, 3⟩,
    ⟨78914639, 2452, 0, 6, 3, 2⟩,
    ⟨97644751, 2451, 2, 24, 3, 3⟩,
    ⟨113065049, 2454, 0, 6, 3, 2⟩,
    ⟨70228211, 2452, 4, 96, 3, 3⟩,
    ⟨87141577, 2453, 4, 96, 3, 3⟩,
    ⟨108303989, 2458, 0, 6, 3, 2⟩,
    ⟨65503349, 2456, 4, 96, 3, 3⟩,
    ⟨72825523, 2459, 2, 24, 3, 3⟩,
    ⟨76224689, 2460, 2, 24, 3, 3⟩,
    ⟨93591997, 2459, 4, 96, 3, 3⟩,
    ⟨108496991, 2460, 4, 96, 3, 3⟩,
    ⟨62702249, 2462, 4, 96, 3, 3⟩,
    ⟨68335297, 2467, 0, 6, 3, 2⟩,
    ⟨84831101, 2468, 0, 6, 3, 2⟩,
    ⟨102828181, 2467, 2, 24, 3, 3⟩,
    ⟨113845349, 2468, 2, 24, 3, 3⟩,
    ⟨69694571, 2468, 4, 96, 3, 3⟩,
    ⟨86761231, 2471, 2, 24, 3, 3⟩,
    ⟨94858889, 2470, 4, 96, 3, 3⟩,
    ⟨116958007, 2475, 0, 6, 3, 2⟩,
    ⟨63705787, 2477, 0, 6, 3, 2⟩,
    ⟨51268961, 2478, 0, 6, 3, 2⟩,
    ⟨114664229, 2474, 4, 96, 3, 3⟩,
    ⟨62816951, 2480, 0, 6, 3, 2⟩,
    ⟨75285517, 2481, 0, 6, 3, 2⟩,
    ⟨76267199, 2482, 0, 6, 3, 2⟩,
    ⟨94843729, 2481, 2, 24, 3, 3⟩,
    ⟨116495651, 2484, 0, 6, 3, 2⟩,
    ⟨69189719, 2486, 0, 6, 3, 2⟩,
    ⟨81783157, 2485, 2, 24, 3, 3⟩,
    ⟨99758819, 2488, 0, 6, 3, 2⟩,
    ⟨123119323, 2487, 2, 24, 3, 3⟩,
    ⟨76944757, 2491, 0, 6, 3, 2⟩,
    ⟨89877791, 2488, 4, 96, 3, 3⟩,
    ⟨111711373, 2491, 2, 24, 3, 3⟩,
    ⟨39660199, 2493, 2, 24, 3, 3⟩,
    ⟨94402663, 2495, 0, 6, 3, 2⟩,
    ⟨116052617, 2494, 2, 24, 3, 3⟩,
    ⟨66403583, 2496, 2, 24, 3, 3⟩,
    ⟨79944283, 2499, 0, 6, 3, 2⟩,
    ⟨89869001, 2496, 4, 96, 3, 3⟩,
    ⟨111890011, 2499, 2, 24, 3, 3⟩,
    ⟨66737707, 2501, 2, 24, 3, 3⟩,
    ⟨74005691, 2500, 4, 96, 3, 3⟩,
    ⟨85936117, 2501, 4, 96, 3, 3⟩,
    ⟨80921723, 2504, 2, 24, 3, 3⟩,
    ⟨78134317, 2505, 2, 24, 3, 3⟩,
    ⟨79991711, 2506, 2, 24, 3, 3⟩,
    ⟨98409943, 2507, 2, 24, 3, 3⟩,
    ⟨122784989, 2508, 2, 24, 3, 3⟩,
    ⟨74679131, 2510, 2, 24, 3, 3⟩,
    ⟨85416493, 2513, 0, 6, 3, 2⟩,
    ⟨101041769, 2510, 4, 96, 3, 3⟩,
    ⟨114573037, 2511, 4, 96, 3, 3⟩,
    ⟨69689497, 2513, 4, 96, 3, 3⟩,
    ⟨86747861, 2514, 4, 96, 3, 3⟩,
    ⟨107397463, 2519, 0, 6, 3, 2⟩,
    ⟨55967833, 2517, 4, 96, 3, 3⟩,
    ⟨65287241, 2522, 0, 6, 3, 2⟩,
    ⟨81270457, 2519, 4, 96, 3, 3⟩,
    ⟨100549601, 2520, 4, 96, 3, 3⟩,
    ⟨121882897, 2521, 4, 96, 3, 3⟩,
    ⟨52764247, 2523, 4, 96, 3, 3⟩,
    ⟨130013017, 2525, 2, 24, 3, 3⟩,
    ⟨68459533, 2527, 2, 24, 3, 3⟩,
    ⟨82144679, 2528, 2, 24, 3, 3⟩,
    ⟨102013663, 2527, 4, 96, 3, 3⟩,
    ⟨124583897, 2530, 2, 24, 3, 3⟩,
    ⟨75482453, 2532, 2, 24, 3, 3⟩,
    ⟨92016877, 2533, 2, 24, 3, 3⟩,
    ⟨112619699, 2536, 0, 6, 3, 2⟩,
    ⟨67509311, 2538, 0, 6, 3, 2⟩,
    ⟨82590187, 2539, 0, 6, 3, 2⟩,
    ⟨90907829, 2540, 0, 6, 3, 2⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 5190511609513286114787594527988091920162924362008625326039055882884689345831184141393879706181319002521499809866844456796623602507288503136397953131584251948051512094510404678371402944102141029425830466039509451228295656704162223215834461954296096504659464323581599754700290793863907204375548508012665508156143800085085155589119387923961215552905460611543758173717241232079065502153815087898086790880083066781163650199495717232430496135714721682697571995046400561109729099261691577993188703825985508850660360622662690363881110079909218863241973421171011139285845125583153757743884403345223371187810149059484239311233228270501582551053242175211733557261768908929697659148705849880151484706879223702950381468944540397993732341830 375655950749750963594794050166441859956201305806153200223296666449545613801007696981094494765810988919274217304886085801694056263744933379815907364094713662630092967376779440600840576767538721943443639994165853850846728373471353207775861836229650437268178022037077820853463021438001889637906492381774840813193247212611930006780179533122269922239174796769058806641589523813283927745471735682150681731765740518432482287180063622566916001197659553695041218225807514443536988654011707435475642063623831171862431945978814321969419718643401018847583870870765524988491357684054442877602844439906459147554778522668790432547713506210039625791232279655980588640142449123428562729171249579125738355504095693863753807385999909536811072468327988123435964778521609025665191665221018583035 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 5190511609513286114787594527988091920162924362008625326039055882884689345831184141393879706181319002521499809866844456796623602507288503136397953131584251948051512094510404678371402944102141029425830466039509451228295656704162223215834461954296096504659464323581599754700290793863907204375548508012665508156143800085085155589119387923961215552905460611543758173717241232079065502153815087898086790880083066781163650199495717232430496135714721682697571995046400561109729099261691577993188703825985508850660360622662690363881110079909218863241973421171011139285845125583153757743884403345223371187810149059484239311233228270501582551053242175211733557261768908929697659148705849880151484706879223702950381468944540397993732341830 < f (k - 1))
    (hhi : f (k - 1) ≤ 375655950749750963594794050166441859956201305806153200223296666449545613801007696981094494765810988919274217304886085801694056263744933379815907364094713662630092967376779440600840576767538721943443639994165853850846728373471353207775861836229650437268178022037077820853463021438001889637906492381774840813193247212611930006780179533122269922239174796769058806641589523813283927745471735682150681731765740518432482287180063622566916001197659553695041218225807514443536988654011707435475642063623831171862431945978814321969419718643401018847583870870765524988491357684054442877602844439906459147554778522668790432547713506210039625791232279655980588640142449123428562729171249579125738355504095693863753807385999909536811072468327988123435964778521609025665191665221018583035) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

