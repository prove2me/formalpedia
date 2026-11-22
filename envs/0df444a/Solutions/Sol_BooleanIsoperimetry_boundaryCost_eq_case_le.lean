-- Prove2me | solution 1 for BooleanIsoperimetry.boundaryCost_eq_case_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:15.01682+00:00
-- url     : https://prove2.me/submissions/eda80bcc-83eb-41de-9619-f9146301a619

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
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    {n a b : ℕ} (ha : a ≤ 2 ^ n) (hb_le_a : b ≤ a) (hcase : a ≤ H n b) :
    max (H n a) b + max (H n b) a = H n a + H n b := by
  have h1 : a ≤ H n a := H_ge_self n a ha
  have h2 : b ≤ H n a := le_trans hb_le_a h1
  have max1 : max (H n a) b = H n a := max_eq_left h2
  have max2 : max (H n b) a = H n b := max_eq_left hcase
  rw [max1, max2]
end BooleanIsoperimetry
