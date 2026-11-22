-- Prove2me | solution 1 for CriticalPortraits.Cycle.window_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:38.777005+00:00
-- url     : https://prove2.me/submissions/aee4e80f-66b4-40b6-aaa3-ebc808721ec1

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
public import Theorems.Thm_CriticalPortraits_Cycle_Q_succ

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits CriticalPortraits.Cycle
variable {n : ℕ}
namespace CriticalPortraits.Cycle
theorem _root_.solution (a : ℕ → ℤ) (hper : ∀ k, a (k + n) = a k)
    (k : ℕ) : Q a (k + n) - Q a k = Q a n - Q a 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : Q a (k + 1 + n) = Q a (k + n) + a (k + n) := by
      have : k + 1 + n = (k + n) + 1 := by ring
      rw [this, Q_succ]
    rw [e1, Q_succ a k, hper k]
    linarith [ih]
end CriticalPortraits.Cycle
