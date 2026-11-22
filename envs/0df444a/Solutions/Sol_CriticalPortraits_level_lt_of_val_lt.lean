-- Prove2me | solution 1 for CriticalPortraits.level_lt_of_val_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:04.683105+00:00
-- url     : https://prove2.me/submissions/29a9317f-533e-4b64-a80d-7f10e6c96086

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Theorems.Thm_CriticalPortraits_level_injOn_fiber
public import Theorems.Thm_CriticalPortraits_val_le_iff_level_le_of_sameFiber


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution [NeZero (d * m)] {x y : ZMod (d * m)}
    (hfib : x.val % m = y.val % m) (h : x.val < y.val) : x.val / m < y.val / m := by
  rcases lt_or_eq_of_le ((val_le_iff_level_le_of_sameFiber hfib).mp h.le) with hlt | heq
  · exact hlt
  · exact absurd (congrArg ZMod.val (level_injOn_fiber hfib heq)) (Nat.ne_of_lt h)
end CriticalPortraits
