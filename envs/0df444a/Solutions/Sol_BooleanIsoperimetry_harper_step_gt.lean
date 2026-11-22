-- Prove2me | solution 1 for BooleanIsoperimetry.harper_step_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:54:44.188795+00:00
-- url     : https://prove2.me/submissions/ff8a7f6a-922b-4b7a-8a0a-880a2d2a2a91

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
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_slack_gt
public import Theorems.Thm_BooleanIsoperimetry_H_one
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_add
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
    (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    H (n + 2) (a + b) ≤ H (n + 1) a + a := by
  have hab_le : a + b ≤ 2 ^ (n + 2) := by
    have h_pow : 2 ^ (n + 2) = 2 ^ (n + 1) + 2 ^ (n + 1) := by
      rw [pow_succ, Nat.mul_two]
    omega
  have ⟨p, q, hp, hq, _, hcasc⟩ := exists_cascade_split (n + 1) (a + b) hab_le
  have hH_succ := H_succ_cascade hcasc
  rw [hH_succ]
  by_cases hq_zero : q = 0
  · have htotal : a + b ≤ 1 := by
      simpa using cascade_split_q_zero_total_le_one (by simpa [hq_zero] using hcasc)
    have hb_zero : b = 0 := by omega
    subst b
    have a_pos : 0 < a := by
      have H_b_zero : H (n + 1) 0 = 0 := H_zero (n + 1)
      omega
    have ha_val : a = 1 := by omega
    subst a
    have hp_val : p = 1 := by have hsum := cascade_split_add hcasc; omega
    simp [hq_zero, hp_val, H_zero, H_one]
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
    exact harper_macaulay_slack_gt n ih ha hb hcasc hq_pos hba hcase
end BooleanIsoperimetry
