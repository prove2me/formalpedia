-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB74_two_grid_square_difference_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:36:28.430664+00:00
-- url     : https://prove2.me/submissions/d3bb56e5-5953-4c7b-ae52-4682bedbd671

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (N : ℕ) (a b : ℕ → ℝ) :
    (Finset.range N).sum (fun i => (a i - b i) ^ 2) ≤
      (Finset.range N).sum (fun i =>
        2 * (a i) ^ 2 + 2 * (b i) ^ 2) := by
  apply Finset.sum_le_sum
  intro i hi
  nlinarith [sq_nonneg (a i + b i)]
