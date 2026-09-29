-- Prove2me | solution 1 for FamousTheorems.eigenvalue_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:02:02.776248+00:00
-- url     : https://prove2.me/submissions/7b4fe188-28a0-4e28-b719-962e15409825

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {K : Type u_1} {n : Type u_2} [inst : NormedField K] [inst_1 : Fintype n] 
    [inst_2 : DecidableEq n] {A : Matrix n n K} {μ : K}, 
    Module.End.HasEigenvalue (Matrix.toLin' A) μ → ∃ k, μ ∈ Metric.closedBall (A k k) (∑ j ∈ Finset.univ.erase k, ‖A k j‖) :=
  @_root_.eigenvalue_mem_ball
