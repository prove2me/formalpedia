-- Prove2me | solution 1 for BooleanIsoperimetry.harper_case_gt_a_ge_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:19.254005+00:00
-- url     : https://prove2.me/submissions/8af0d551-7e56-464e-a3a1-af56a30fd734

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_lower_le_of_neighbor_lt

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) {a b p q : ℕ}
    (hq_pos : 1 ≤ q) (hcase : H (n + 1) b < a)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) : p ≤ a :=
  cascade_lower_le_of_neighbor_lt hcasc hq_pos hcase
end BooleanIsoperimetry
