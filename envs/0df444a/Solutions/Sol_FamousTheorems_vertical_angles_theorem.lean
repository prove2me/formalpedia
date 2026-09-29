-- Prove2me | solution 1 for FamousTheorems.vertical_angles_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T08:10:51.603876+00:00
-- url     : https://prove2.me/submissions/14d50a09-c257-4108-a31c-3644e7eb01ab

import Mathlib

open EuclideanGeometry

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : ∠ p₁ p₅ p₃ = Real.pi) (h₂ : ∠ p₂ p₅ p₄ = Real.pi) : ∠ p₁ p₅ p₂ = ∠ p₃ p₅ p₄ := by
  exact EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi h₁ h₂
