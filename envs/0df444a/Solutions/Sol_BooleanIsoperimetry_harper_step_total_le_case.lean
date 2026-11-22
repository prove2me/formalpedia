-- Prove2me | solution 1 for BooleanIsoperimetry.harper_step_total_le_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:56:38.560612+00:00
-- url     : https://prove2.me/submissions/7977e041-0163-4f2c-94d4-4bf7a647f419

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
public import Theorems.Thm_BooleanIsoperimetry_boundaryCostH_eq_H_add_slack
public import Theorems.Thm_BooleanIsoperimetry_harper_step_le
public import Theorems.Thm_BooleanIsoperimetry_harper_step_gt
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self


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
    (hba : b ≤ a) :
    H (n + 2) (a + b) ≤ boundaryCostH (n + 1) a b := by
  rw [boundaryCostH_eq_H_add_slack]
  have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
  by_cases hcase : a ≤ H (n + 1) b
  · have h := harper_step_le n ih ha hb hba hcase
    omega
  · have hcase' : H (n + 1) b < a := Nat.lt_of_not_le hcase
    have h := harper_step_gt n ih ha hb hba hcase'
    omega
end BooleanIsoperimetry
