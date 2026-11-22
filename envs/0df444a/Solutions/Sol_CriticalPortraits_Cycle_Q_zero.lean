-- Prove2me | solution 1 for CriticalPortraits.Cycle.Q_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:46.828058+00:00
-- url     : https://prove2.me/submissions/2e5bcfb3-9cf7-4a15-bf29-a6b9f71b1cfc

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits CriticalPortraits.Cycle
variable {n : ℕ}
namespace CriticalPortraits.Cycle
theorem _root_.solution (a : ℕ → ℤ) : Q a 0 = 0 := by simp [Q]
end CriticalPortraits.Cycle
