-- Prove2me | solution 1 for FamousTheorems.isosceles_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T22:59:34.18085+00:00
-- url     : https://prove2.me/submissions/6442822e-213c-4dc6-b9a5-2714442dea37

import Mathlib.Geometry.Euclidean.Triangle

open scoped EuclideanGeometry Real

theorem solution
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂ := by
  exact EuclideanGeometry.angle_eq_angle_of_dist_eq h
