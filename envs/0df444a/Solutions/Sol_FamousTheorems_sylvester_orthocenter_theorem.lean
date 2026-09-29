-- Prove2me | solution 1 for FamousTheorems.sylvester_orthocenter_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:52:36.730275+00:00
-- url     : https://prove2.me/submissions/28207130-2187-44ae-bef9-9579a981ecab

import Mathlib

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (t : Affine.Triangle ℝ P) : t.orthocenter -ᵥ t.circumcenter = ∑ i, (t.points i -ᵥ t.circumcenter) := by
  exact Affine.Triangle.orthocenter_vsub_circumcenter_eq_sum_vsub t
