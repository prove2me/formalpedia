-- Prove2me | solution 1 for FamousTheorems.dist_sq_mul_dist_add_dist_sq_mul_dist
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:44.610525+00:00
-- url     : https://prove2.me/submissions/8bb7f995-41f5-4773-8ff0-b4d04b35ddc3

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] 
    [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] (a b c p : P), 
    EuclideanGeometry.angle b p c = Real.pi → 
    dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p = dist b c * (dist a p ^ 2 + dist b p * dist c p) :=
  @_root_.EuclideanGeometry.dist_sq_mul_dist_add_dist_sq_mul_dist
