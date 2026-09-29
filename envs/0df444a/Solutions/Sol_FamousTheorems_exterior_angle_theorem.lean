-- Prove2me | solution 1 for FamousTheorems.exterior_angle_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:24:06.481812+00:00
-- url     : https://prove2.me/submissions/d9c5850a-819e-4887-87c0-7bb3ec714d98

import Mathlib

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ p₃ : P} (p : P) (h : Sbtw ℝ p p₁ p₂) :
    EuclideanGeometry.angle p₃ p₁ p = EuclideanGeometry.angle p₁ p₃ p₂ + EuclideanGeometry.angle p₃ p₂ p₁ :=
  EuclideanGeometry.exterior_angle_eq_angle_add_angle p h
