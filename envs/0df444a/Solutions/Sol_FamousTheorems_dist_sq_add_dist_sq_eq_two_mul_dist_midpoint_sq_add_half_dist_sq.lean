-- Prove2me | solution 1 for FamousTheorems.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:02:01.739792+00:00
-- url     : https://prove2.me/submissions/8797e306-250e-4dd8-995e-b1065fc18f82

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {V : Type u_1} {P : Type u_2} 
    [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] 
    (a b c : P), dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :=
  @_root_.EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
