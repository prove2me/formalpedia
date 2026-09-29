-- Prove2me | solution 1 for FamousTheorems.isosceles_triangle_converse_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:10:44.857812+00:00
-- url     : https://prove2.me/submissions/5d2faaa4-aa96-4df0-9854-ff0b65c26c4b

import Mathlib

open EuclideanGeometry

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {p₁ p₂ p₃ : P}
    (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂) (hpi : ∠ p₂ p₁ p₃ ≠ Real.pi) : dist p₁ p₂ = dist p₁ p₃ :=
  dist_eq_of_angle_eq_angle_of_angle_ne_pi h hpi
