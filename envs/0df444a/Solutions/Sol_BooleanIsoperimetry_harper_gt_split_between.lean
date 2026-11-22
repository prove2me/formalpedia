-- Prove2me | solution 1 for BooleanIsoperimetry.harper_gt_split_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:10.613805+00:00
-- url     : https://prove2.me/submissions/aef2896b-90a2-44a3-84d9-78c49b2f5ace

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_harper_case_gt_a_ge_p
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le_p
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) {a b p q : ℕ}
    (hq_pos : 1 ≤ q) (hcase : H (n + 1) b < a)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    b ≤ q ∧ q ≤ p ∧ p ≤ a := by
  have hpa : p ≤ a := harper_case_gt_a_ge_p n hq_pos hcase hcasc
  have hqp : q ≤ p := cascade_q_le_p hcasc
  have hsum : p + q = a + b := cascade_split_add hcasc
  exact ⟨by omega, hqp, hpa⟩
end BooleanIsoperimetry
