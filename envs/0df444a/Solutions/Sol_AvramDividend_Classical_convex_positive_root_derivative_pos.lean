-- Prove2me | solution 1 for AvramDividend.Classical.convex_positive_root_derivative_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:45:59.801984+00:00
-- url     : https://prove2.me/submissions/b36f1fbd-6909-4c7f-8738-c2d7f6b36c41

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The derivative of a convex Laplace exponent is positive at a positive root. -/
theorem solution
    (f : ℝ → ℝ) (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f)
    (hzero : f 0 = 0) (hroot : f φ = q)
    (hderiv : DifferentiableAt ℝ f φ) :
    0 < deriv f φ := by
  have hslope :
      slope f 0 φ ≤ deriv f φ :=
    hconv.slope_le_deriv (by simp) (le_of_lt hφ) hφ hderiv
  have hsl_eq : slope f 0 φ = q / φ := by
    rw [slope_def_field, hzero, hroot]
    ring
  have hsl_pos : 0 < slope f 0 φ := by
    rw [hsl_eq]
    positivity
  exact lt_of_lt_of_le hsl_pos hslope
