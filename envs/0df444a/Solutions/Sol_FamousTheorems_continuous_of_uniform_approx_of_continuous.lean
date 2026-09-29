-- Prove2me | solution 1 for FamousTheorems.continuous_of_uniform_approx_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:11.517898+00:00
-- url     : https://prove2.me/submissions/7e0ac0a0-bf6f-46c8-8f19-5f8e555b9772

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] 
    [inst_1 : UniformSpace β] {f : α → β}, 
    (∀ u ∈ uniformity β, ∃ F, Continuous F ∧ ∀ (y : α), (f y, F y) ∈ u) → Continuous f :=
  @_root_.continuous_of_uniform_approx_of_continuous
