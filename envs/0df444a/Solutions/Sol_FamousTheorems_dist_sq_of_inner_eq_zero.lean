-- Prove2me | solution 1 for FamousTheorems.dist_sq_of_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:55:30.41109+00:00
-- url     : https://prove2.me/submissions/27cd7bfb-f8e2-4905-aec9-5f3df3417d74

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] 
    [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {a b p : P}, 
    inner ℝ (p -ᵥ a) (b -ᵥ a) = 0 → dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2 :=
  @_root_.dist_sq_of_inner_eq_zero
