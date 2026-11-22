-- Prove2me | solution 1 for CriticalPortraits.hiV_lt_d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:01.262492+00:00
-- url     : https://prove2.me/submissions/c22f11f5-6aa6-46bb-8a54-c7f52f6ce830

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
theorem _root_.solution [NeZero (d * m)] (_hm : 0 < m) (x : ZMod (d * m)) : hiV x < d := by
  unfold hiV
  have hval : x.val < d * m := ZMod.val_lt x
  have hval' : x.val < m * d := lt_of_lt_of_le hval (le_of_eq (Nat.mul_comm d m))
  exact Nat.div_lt_of_lt_mul hval'
end CriticalPortraits
