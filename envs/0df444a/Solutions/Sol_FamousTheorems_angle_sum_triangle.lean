-- Prove2me | solution 1 for FamousTheorems.angle_sum_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T23:01:23.720976+00:00
-- url     : https://prove2.me/submissions/df3c9723-581a-43f6-93a6-ba44a73af94c

import Mathlib.Geometry.Euclidean.Triangle

open scoped EuclideanGeometry Real

theorem solution
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ : P} (p₃ : P) (h : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π := by
  exact EuclideanGeometry.angle_add_angle_add_angle_eq_pi p₃ h
