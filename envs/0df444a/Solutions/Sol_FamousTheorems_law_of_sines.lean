-- Prove2me | solution 1 for FamousTheorems.law_of_sines
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:25:50.610987+00:00
-- url     : https://prove2.me/submissions/cecc9d7d-b4f3-4c86-bb16-eb3eb0ce37c3

import Mathlib

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (p₁ p₂ p₃ : P) :
    Real.sin (EuclideanGeometry.angle p₁ p₂ p₃) * dist p₂ p₃ =
      Real.sin (EuclideanGeometry.angle p₃ p₁ p₂) * dist p₃ p₁ :=
  EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist p₁ p₂ p₃
