-- Prove2me | solution 2 for FamousTheorems.intersecting_chords
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T23:05:43.535437+00:00
-- url     : https://prove2.me/submissions/1d40ed7e-a26d-4f93-8be7-93536394d235

import Mathlib.Geometry.Euclidean.Sphere.Power

open scoped EuclideanGeometry Real

theorem solution
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {a b c d p : P} (h : EuclideanGeometry.Cospherical ({a, b, c, d} : Set P))
    (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p := by
  exact EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi h hapb hcpd
