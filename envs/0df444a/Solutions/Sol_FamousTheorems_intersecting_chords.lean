-- Prove2me | solution 1 for FamousTheorems.intersecting_chords
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:04:24.27132+00:00
-- url     : https://prove2.me/submissions/3000ca74-0255-4af5-8281-036c77cebca1

import Mathlib

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Real Topology EuclideanGeometry RealInnerProductSpace Affine

theorem solution
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {a b c d p : P} (h : EuclideanGeometry.Cospherical ({a, b, c, d} : Set P))
    (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p :=
  EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi h hapb hcpd
