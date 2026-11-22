-- Prove2me | solution 1 for CriticalPortraits.Cycle.Q_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:04.754916+00:00
-- url     : https://prove2.me/submissions/134fa3d5-714b-42ac-b02c-f23d7d840ef6

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
public import Theorems.Thm_CriticalPortraits_Cycle_Q_zero
public import Theorems.Thm_CriticalPortraits_Cycle_window_sum

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits CriticalPortraits.Cycle
variable {n : ℕ}
namespace CriticalPortraits.Cycle
theorem _root_.solution (a : ℕ → ℤ) (hper : ∀ k, a (k + n) = a k) (hsum : Q a n = 1)
    (k : ℕ) : Q a (k + n) = Q a k + 1 := by
  have := window_sum a hper k
  rw [Q_zero] at this
  linarith [this, hsum]
end CriticalPortraits.Cycle
