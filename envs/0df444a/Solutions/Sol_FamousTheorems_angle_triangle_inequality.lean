-- Prove2me | solution 1 for FamousTheorems.angle_triangle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:56:42.568979+00:00
-- url     : https://prove2.me/submissions/0a812441-6c72-431b-914f-34e7e8266ce3

import Mathlib

open EuclideanGeometry

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (p p₁ p₂ p₃ : P) : ∠ p₁ p p₃ ≤ ∠ p₁ p p₂ + ∠ p₂ p p₃ := by
  exact EuclideanGeometry.angle_le_angle_add_angle p p₁ p₂ p₃
