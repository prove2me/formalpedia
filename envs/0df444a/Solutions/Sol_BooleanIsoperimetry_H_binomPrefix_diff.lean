-- Prove2me | solution 1 for BooleanIsoperimetry.H_binomPrefix_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:40.941118+00:00
-- url     : https://prove2.me/submissions/ec43501a-461d-4e19-beba-1cd6883cc1a6

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) (hr : 2 ≤ r) :
    H n (binomPrefix n r) - H n (binomPrefix n (r - 1)) = Nat.choose n r := by
  have hr_pos : 1 ≤ r := by omega
  have hr_pred : 1 ≤ r - 1 := by omega
  rw [H_binomPrefix n r hr_pos, H_binomPrefix n (r - 1) hr_pred]
  rw [show r - 1 + 1 = r by omega]
  rw [binomPrefix_succ]
  omega
end BooleanIsoperimetry
