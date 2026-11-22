-- Prove2me | solution 1 for BooleanIsoperimetry.HIncrement_eq_gShift_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:27.054849+00:00
-- url     : https://prove2.me/submissions/3f1967ca-bb1e-4515-b74c-a5839f8446ca

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
public import Theorems.Thm_BooleanIsoperimetry_H_increment_eq_gShift_inv


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n p : ℕ) (w : Cube n) (hw : rank w = p) :
    HIncrement n p =
      (Finset.filter (fun v => gShift v = w) (Finset.univ : Finset (Cube n))).card := by
  unfold HIncrement
  rw [H_increment_eq_gShift_inv n p w hw]
  exact Nat.add_sub_cancel_left (H n p) _
end BooleanIsoperimetry
