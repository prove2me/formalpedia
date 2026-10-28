-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_down_count_le_of_uniform_close
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:41:59.385457+00:00
-- url     : https://prove2.me/submissions/8e934a9c-cc3d-484e-8a5e-f534f9355642

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
open scoped NNReal BigOperators

theorem solution
    (grid : Finset (ℝ≥0 × ℝ≥0)) (a ε : ℝ)
    (f g : ℝ≥0 → ℝ)
    (hclose : ∀ t, |f t - g t| ≤ ε) :
    (∑ ij ∈ grid,
      if f ij.2 - f ij.1 < -(a + 2 * ε) then (1 : ℕ) else 0) ≤
    ∑ ij ∈ grid,
      if g ij.2 - g ij.1 < -a then (1 : ℕ) else 0 := by
  refine Finset.sum_le_sum ?_
  intro ij hij
  by_cases hf : f ij.2 - f ij.1 < -(a + 2 * ε)
  · have hlo := (abs_le.mp (hclose ij.2)).1
    have hhi := (abs_le.mp (hclose ij.1)).2
    have hg : g ij.2 - g ij.1 < -a := by linarith
    rw [if_pos hf, if_pos hg]
  · rw [if_neg hf]
    exact Nat.zero_le _