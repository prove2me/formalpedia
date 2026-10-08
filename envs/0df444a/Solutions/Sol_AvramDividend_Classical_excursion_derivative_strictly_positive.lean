-- Prove2me | solution 1 for AvramDividend.Classical.excursion_derivative_strictly_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:18:56.247779+00:00
-- url     : https://prove2.me/submissions/dc66c4d3-536b-460e-8967-a6349aae6c85

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (W : ℝ → ℝ) (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hW : ∀ x : ℝ, 0 < x → 0 < W x)
    (hderiv : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x))) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  intro x hx
  rw [hderiv x hx]
  have htail : 0 ≤ μ.real (Ici x) := by
    exact ENNReal.toReal_nonneg
  exact mul_pos (hW x hx) (by linarith)
