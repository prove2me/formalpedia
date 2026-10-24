-- Prove2me | solution 1 for AvramDividend.Classical.stopped_renewal_finite_geometric_budget_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:55:28.508188+00:00
-- url     : https://prove2.me/submissions/55738f7f-7953-4ffc-99ac-74ac67f785e3

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Finite first-record renewal weights satisfy the exact geometric budget identity. -/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (p : ℝ) (n : ℕ) :
    (1 - p) * (∑ i ∈ Finset.range n, p ^ i) = 1 - p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ, mul_add, ih]
      ring
