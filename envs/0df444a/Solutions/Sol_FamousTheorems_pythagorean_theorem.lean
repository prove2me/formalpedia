-- Prove2me | solution 1 for FamousTheorems.pythagorean_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T22:46:14.550303+00:00
-- url     : https://prove2.me/submissions/10a21268-cbfd-450d-bd55-0e111c6cdd2c

import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

open scoped EuclideanGeometry Real

theorem solution
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      ∠ p₁ p₂ p₃ = π / 2 := by
  exact EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two p₁ p₂ p₃
