-- Prove2me | solution 1 for AvramDividend.Classical.avram_mixed_source13_finite_grid_factorial_telescoping_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:24:11.489361+00:00
-- url     : https://prove2.me/submissions/d04e1b6f-b4d3-4094-a03c-4bcb810c9390

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open BigOperators
noncomputable section

theorem solution
    (k : ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ Finset.range k, a i) * ((∑ i ∈ Finset.range k, a i) - 1) =
      (∑ i ∈ Finset.range k, a i * (a i - 1)) +
        2 * (∑ i ∈ Finset.range k, (∑ j ∈ Finset.range i, a j) * a i) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [Finset.sum_range_succ]
      calc
        _ = (∑ i ∈ Finset.range k, a i) *
              ((∑ i ∈ Finset.range k, a i) - 1) +
            a k * (a k - 1) +
            2 * ((∑ j ∈ Finset.range k, a j) * a k) := by ring
        _ = _ := by rw [ih]; ring
