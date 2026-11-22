-- Prove2me | solution 1 for BooleanIsoperimetry.harper_step_le_sum_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:55:20.452823+00:00
-- url     : https://prove2.me/submissions/35c87db4-2b24-4921-8d04-7fa4eaf85bda

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_q_zero_total_le_one
public import Theorems.Thm_BooleanIsoperimetry_harper_step_le_canonical_sum
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 2) (a + b) ≤ H (n + 1) a + H (n + 1) b := by
  obtain ⟨p, q, hp, hq, _hpq, hcasc⟩ :=
    exists_cascade_split (n + 1) (a + b) (by
      have hsum : a + b ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := Nat.add_le_add ha hb
      have hpow : 2 ^ (n + 2) = 2 ^ (n + 1) + 2 ^ (n + 1) := by
        rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
        ring
      rwa [hpow])
  by_cases hq_zero : q = 0
  · have htotal : a + b ≤ 1 := by
      simpa [hq_zero] using cascade_split_q_zero_total_le_one (by simpa [hq_zero] using hcasc)
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
    · have hb_zero : b = 0 := by omega
      subst b
      simp [H_zero]
    · have hb_zero : b = 0 := by omega
      subst b
      simp [H_zero] at hcase
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    have hcanon :
        H (n + 2) (a + b) = H (n + 1) p + H (n + 1) q := by
      have hsucc : H (n + 2) (a + b)
          = max (H (n + 1) p) q + max (H (n + 1) q) p := by
        rw [show n + 2 = n + 1 + 1 from rfl]
        exact H_succ_cascade hcasc
      have hcollapse :
          max (H (n + 1) p) q + max (H (n + 1) q) p =
            H (n + 1) p + H (n + 1) q :=
        canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc
      rw [hsucc, hcollapse]
    rw [hcanon]
    exact harper_step_le_canonical_sum n ih ha hb hcasc hba hcase
end BooleanIsoperimetry
