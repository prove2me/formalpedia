-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_1732_through_1859
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:21:22.425778+00:00
-- url     : https://prove2.me/submissions/5a4d6e8d-f703-4ba1-826a-1767a6ec6ff1

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
  [ ⟨78766603, 2695, 0, 6, 3, 2⟩,
    ⟨96935837, 2694, 2, 24, 3, 3⟩,
    ⟨107799067, 2697, 0, 6, 3, 2⟩,
    ⟨40627837, 2699, 0, 6, 3, 2⟩,
    ⟨95467627, 2695, 4, 96, 3, 3⟩,
    ⟨117778151, 2696, 4, 96, 3, 3⟩,
    ⟨68084963, 2700, 2, 24, 3, 3⟩,
    ⟨56691139, 2701, 2, 24, 3, 3⟩,
    ⟨60030197, 2702, 2, 24, 3, 3⟩,
    ⟨69933517, 2701, 4, 96, 3, 3⟩,
    ⟨80068631, 2706, 0, 6, 3, 2⟩,
    ⟨94577827, 2703, 4, 96, 3, 3⟩,
    ⟨111765851, 2708, 0, 6, 3, 2⟩,
    ⟨65951609, 2710, 0, 6, 3, 2⟩,
    ⟨75324343, 2711, 0, 6, 3, 2⟩,
    ⟨77428301, 2712, 0, 6, 3, 2⟩,
    ⟨95162167, 2713, 0, 6, 3, 2⟩,
    ⟨117440339, 2712, 2, 24, 3, 3⟩,
    ⟨59754251, 2712, 4, 96, 3, 3⟩,
    ⟨54892111, 2715, 2, 24, 3, 3⟩,
    ⟨66355379, 2718, 0, 6, 3, 2⟩,
    ⟨78909247, 2715, 4, 96, 3, 3⟩,
    ⟨93530837, 2718, 2, 24, 3, 3⟩,
    ⟨105293233, 2717, 4, 96, 3, 3⟩,
    ⟨125033999, 2718, 4, 96, 3, 3⟩,
    ⟨69994619, 2720, 4, 96, 3, 3⟩,
    ⟨76375627, 2721, 4, 96, 3, 3⟩,
    ⟨93017513, 2724, 2, 24, 3, 3⟩,
    ⟨116141023, 2727, 0, 6, 3, 2⟩,
    ⟨67766221, 2727, 2, 24, 3, 3⟩,
    ⟨77446979, 2726, 4, 96, 3, 3⟩,
    ⟨88969393, 2731, 0, 6, 3, 2⟩,
    ⟨105642101, 2730, 2, 24, 3, 3⟩,
    ⟨129084037, 2729, 4, 96, 3, 3⟩,
    ⟨69657967, 2735, 0, 6, 3, 2⟩,
    ⟨85556651, 2736, 0, 6, 3, 2⟩,
    ⟨105859543, 2737, 0, 6, 3, 2⟩,
    ⟨131886473, 2736, 2, 24, 3, 3⟩,
    ⟨79353431, 2740, 0, 6, 3, 2⟩,
    ⟨95069893, 2739, 2, 24, 3, 3⟩,
    ⟨114031241, 2742, 0, 6, 3, 2⟩,
    ⟨65336441, 2742, 2, 24, 3, 3⟩,
    ⟨79296391, 2739, 6, 384, 3, 3⟩,
    ⟨98884913, 2744, 2, 24, 3, 3⟩,
    ⟨120612937, 2741, 6, 384, 3, 3⟩,
    ⟨74539057, 2745, 4, 96, 3, 3⟩,
    ⟨92608259, 2748, 2, 24, 3, 3⟩,
    ⟨100007797, 2747, 4, 96, 3, 3⟩,
    ⟨117197621, 2746, 6, 384, 3, 3⟩,
    ⟨68825969, 2752, 2, 24, 3, 3⟩,
    ⟨83882317, 2755, 0, 6, 3, 2⟩,
    ⟨93749561, 2756, 0, 6, 3, 2⟩,
    ⟨111986713, 2755, 2, 24, 3, 3⟩,
    ⟨67385797, 2753, 6, 384, 3, 3⟩,
    ⟨58944731, 2760, 0, 6, 3, 2⟩,
    ⟨69050551, 2759, 2, 24, 3, 3⟩,
    ⟨85343849, 2756, 6, 384, 3, 3⟩,
    ⟨83568703, 2759, 4, 96, 3, 3⟩,
    ⟨102310721, 2758, 6, 384, 3, 3⟩,
    ⟨127858537, 2761, 4, 96, 3, 3⟩,
    ⟨72848959, 2761, 6, 384, 3, 3⟩,
    ⟨81497561, 2762, 6, 384, 3, 3⟩,
    ⟨99457993, 2769, 0, 6, 3, 2⟩,
    ⟨122517221, 2766, 4, 96, 3, 3⟩,
    ⟨64189691, 2772, 0, 6, 3, 2⟩,
    ⟨80093413, 2773, 0, 6, 3, 2⟩,
    ⟨95425271, 2770, 4, 96, 3, 3⟩,
    ⟨117882673, 2775, 0, 6, 3, 2⟩,
    ⟨71648713, 2773, 4, 96, 3, 3⟩,
    ⟨87503789, 2774, 4, 96, 3, 3⟩,
    ⟨108857197, 2773, 6, 384, 3, 3⟩,
    ⟨56934133, 2775, 6, 384, 3, 3⟩,
    ⟨69870209, 2780, 2, 24, 3, 3⟩,
    ⟨84158497, 2779, 4, 96, 3, 3⟩,
    ⟨103622741, 2780, 4, 96, 3, 3⟩,
    ⟨127304131, 2779, 6, 384, 3, 3⟩,
    ⟨50551759, 2785, 2, 24, 3, 3⟩,
    ⟨123146377, 2781, 6, 384, 3, 3⟩,
    ⟨68506117, 2789, 0, 6, 3, 2⟩,
    ⟨85600673, 2784, 6, 384, 3, 3⟩,
    ⟨106968637, 2791, 0, 6, 3, 2⟩,
    ⟨132645551, 2788, 4, 96, 3, 3⟩,
    ⟨72009071, 2790, 4, 96, 3, 3⟩,
    ⟨85540333, 2795, 0, 6, 3, 2⟩,
    ⟨104566421, 2792, 4, 96, 3, 3⟩,
    ⟨127167067, 2793, 4, 96, 3, 3⟩,
    ⟨76176097, 2793, 6, 384, 3, 3⟩,
    ⟨88547231, 2798, 2, 24, 3, 3⟩,
    ⟨97153831, 2795, 6, 384, 3, 3⟩,
    ⟨119463059, 2796, 6, 384, 3, 3⟩,
    ⟨64027547, 2798, 6, 384, 3, 3⟩,
    ⟨53860087, 2801, 4, 96, 3, 3⟩,
    ⟨62960171, 2802, 4, 96, 3, 3⟩,
    ⟨74681479, 2801, 6, 384, 3, 3⟩,
    ⟨84359801, 2806, 2, 24, 3, 3⟩,
    ⟨99889411, 2803, 6, 384, 3, 3⟩,
    ⟨108832811, 2810, 0, 6, 3, 2⟩,
    ⟨62028719, 2808, 4, 96, 3, 3⟩,
    ⟨77338021, 2811, 2, 24, 3, 3⟩,
    ⟨82441739, 2812, 2, 24, 3, 3⟩,
    ⟨101653147, 2811, 4, 96, 3, 3⟩,
    ⟨121566551, 2814, 2, 24, 3, 3⟩,
    ⟨75728249, 2818, 0, 6, 3, 2⟩,
    ⟨89979457, 2819, 0, 6, 3, 2⟩,
    ⟨104410091, 2818, 2, 24, 3, 3⟩,
    ⟨125993521, 2815, 6, 384, 3, 3⟩,
    ⟨72787237, 2819, 4, 96, 3, 3⟩,
    ⟨84776477, 2822, 2, 24, 3, 3⟩,
    ⟨102194047, 2825, 0, 6, 3, 2⟩,
    ⟨118838441, 2822, 4, 96, 3, 3⟩,
    ⟨67521239, 2824, 4, 96, 3, 3⟩,
    ⟨65153323, 2827, 2, 24, 3, 3⟩,
    ⟨79134203, 2824, 6, 384, 3, 3⟩,
    ⟨94359913, 2831, 0, 6, 3, 2⟩,
    ⟨108379241, 2828, 4, 96, 3, 3⟩,
    ⟨63928829, 2830, 4, 96, 3, 3⟩,
    ⟨77802223, 2835, 0, 6, 3, 2⟩,
    ⟨90141341, 2834, 2, 24, 3, 3⟩,
    ⟨103690711, 2831, 6, 384, 3, 3⟩,
    ⟨122056439, 2834, 4, 96, 3, 3⟩,
    ⟨75210077, 2834, 6, 384, 3, 3⟩,
    ⟨88102447, 2841, 0, 6, 3, 2⟩,
    ⟨109947389, 2836, 6, 384, 3, 3⟩,
    ⟨61560797, 2842, 2, 24, 3, 3⟩,
    ⟨71629027, 2845, 0, 6, 3, 2⟩,
    ⟨72347669, 2844, 2, 24, 3, 3⟩,
    ⟨90417463, 2843, 4, 96, 3, 3⟩,
    ⟨106474229, 2848, 0, 6, 3, 2⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 6802687467857223928666416896072006166970798354323982721730818052242995938973734099166809510086698117810202780424129548904912950420138909605881018637422801565030100590719538116961276870323518837437867788633689332009052293300508848229737910785823708652851099536871351262841686997468404515250992136666895980700019323886852373675062663212276486816565454021209378871960729438522238577067632182496863719363462094415019359356262687234456773233891336837656700621831265193032151704028375831643538616821854926261424080330631916324515234991083524553397244180928409513670544643538845218817608158191830270907960834215547551230702427695275795851175412004515242842358304872581998365710929358669758196573356198703816775019045200732198920975412008396219093076587196845310795373565455029930798310387893491284498734835872772039117939671110 229441596004525787074057815376097017466674686601421458897492804628541399987510093503500379547741769129945712877683439843933664736583512090480153080040512637505077928726412425811870943524020061663717739092928353120362643894560610604218989727495245603281634269069484527728012080648401737119721391885036736445198417877017416112323814534186749474890488083597073550666913589614805105258635726938270113746044925711169159724903681784216096088592170639694370041990359745392910489935469001479588773057257848877320573893427257691511336921307651129592965376048609748173203860396872451822179984813716276132054685366357482883292556052525044737553466115731492611853921897874444580445518812292686053808105422053737527804829907547091527141762273461124318305170667603630885106689457260075747776619197308939957566775112449045864890553930492397081661059463786661144350620139655517962235 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 6802687467857223928666416896072006166970798354323982721730818052242995938973734099166809510086698117810202780424129548904912950420138909605881018637422801565030100590719538116961276870323518837437867788633689332009052293300508848229737910785823708652851099536871351262841686997468404515250992136666895980700019323886852373675062663212276486816565454021209378871960729438522238577067632182496863719363462094415019359356262687234456773233891336837656700621831265193032151704028375831643538616821854926261424080330631916324515234991083524553397244180928409513670544643538845218817608158191830270907960834215547551230702427695275795851175412004515242842358304872581998365710929358669758196573356198703816775019045200732198920975412008396219093076587196845310795373565455029930798310387893491284498734835872772039117939671110 < f (k - 1))
    (hhi : f (k - 1) ≤ 229441596004525787074057815376097017466674686601421458897492804628541399987510093503500379547741769129945712877683439843933664736583512090480153080040512637505077928726412425811870943524020061663717739092928353120362643894560610604218989727495245603281634269069484527728012080648401737119721391885036736445198417877017416112323814534186749474890488083597073550666913589614805105258635726938270113746044925711169159724903681784216096088592170639694370041990359745392910489935469001479588773057257848877320573893427257691511336921307651129592965376048609748173203860396872451822179984813716276132054685366357482883292556052525044737553466115731492611853921897874444580445518812292686053808105422053737527804829907547091527141762273461124318305170667603630885106689457260075747776619197308939957566775112449045864890553930492397081661059463786661144350620139655517962235) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

