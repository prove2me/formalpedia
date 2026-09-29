-- Prove2me | solution 1 for FamousTheorems.ptolemy_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:58:53.885923+00:00
-- url     : https://prove2.me/submissions/cdabdd88-e49a-4c13-892a-3d95f451d9ec

import Mathlib

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (a b c d : P) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d :=
  EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist a b c d
