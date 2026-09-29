-- Prove2me | solution 1 for FamousTheorems.nine_point_circle_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:22:30.841835+00:00
-- url     : https://prove2.me/submissions/b0fb1e1e-5bf4-43c1-9de9-a7f0c04cc707

import Mathlib

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (s : Affine.Triangle ℝ P) : ∃ S : EuclideanGeometry.Sphere P,
      (∀ i, s.faceOppositeCentroid i ∈ S) ∧ (∀ i, s.altitudeFoot i ∈ S) ∧
        ∀ i, midpoint ℝ s.orthocenter (s.points i) ∈ S :=
  ⟨s.ninePointCircle, fun i => Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle s i,
    fun i => Affine.Triangle.altitudeFoot_mem_ninePointCircle s i,
    fun i => by rw [← Affine.Triangle.eulerPoint_eq_midpoint]; exact Affine.Simplex.eulerPoint_mem_ninePointCircle s i⟩
