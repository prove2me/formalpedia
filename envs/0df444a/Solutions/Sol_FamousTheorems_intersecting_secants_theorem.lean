-- Prove2me | solution 1 for FamousTheorems.intersecting_secants_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T08:09:16.684+00:00
-- url     : https://prove2.me/submissions/1a182a04-60be-4880-aeba-2cf2d7142714

import Mathlib

open EuclideanGeometry

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {a b c d p : P} (hcos : Cospherical ({a, b, c, d} : Set P)) (hab : a ≠ b) (hcd : c ≠ d)
    (hapb : ∠ a p b = 0) (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p := by
  exact EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero hcos hab hcd hapb hcpd
