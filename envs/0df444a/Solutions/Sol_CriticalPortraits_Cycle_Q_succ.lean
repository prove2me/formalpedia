-- Prove2me | solution 1 for CriticalPortraits.Cycle.Q_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:54.045797+00:00
-- url     : https://prove2.me/submissions/ca53f2b2-2102-4ee0-94cd-f6855d1cb5cf

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
theorem _root_.solution (a : ℕ → ℤ) (k : ℕ) : Q a (k + 1) = Q a k + a k := by
  simp [Q, Finset.sum_range_succ]
end CriticalPortraits.Cycle
