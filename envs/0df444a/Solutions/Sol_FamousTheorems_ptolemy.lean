-- Prove2me | solution 1 for FamousTheorems.ptolemy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T22:56:42.176295+00:00
-- url     : https://prove2.me/submissions/f56d4a98-5929-453a-9475-c5ff2eacd18c

import Mathlib.Geometry.Euclidean.Sphere.Ptolemy

open scoped EuclideanGeometry Real

theorem solution
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {a b c d p : P} (h : EuclideanGeometry.Cospherical ({a, b, c, d} : Set P))
    (hapc : ∠ a p c = π) (hbpd : ∠ b p d = π) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d := by
  exact EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical h hapc hbpd
