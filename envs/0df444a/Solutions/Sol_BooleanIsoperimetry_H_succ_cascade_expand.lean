-- Prove2me | solution 1 for BooleanIsoperimetry.H_succ_cascade_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:18.782341+00:00
-- url     : https://prove2.me/submissions/392ee207-343b-4afa-8c77-2925d7093fe3

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_max_eq_right
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le_p


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x x0 x1 : ℕ} (hx : CascadeSplit n x x0 x1) (hx0 : x0 ≤ 2 ^ n) :
    max (H n x0) x1 + max (H n x1) x0 = H n x0 + if 1 ≤ x1 then H n x1 else x0 := by
  have h1 : max (H n x0) x1 = H n x0 := by
    apply max_eq_left
    exact le_trans (cascade_q_le_p hx) (H_ge_self n x0 hx0)
  rw [h1, cascade_max_eq_right hx]
end BooleanIsoperimetry
