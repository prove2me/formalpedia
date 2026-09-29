-- Prove2me | solution 1 for FamousTheorems.measure_limsup_attop_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:25.516381+00:00
-- url     : https://prove2.me/submissions/754f2936-68d2-4e6a-9bb8-e189a6a775d9

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] 
    [MeasureTheory.OuterMeasureClass F α] {μ : F} {s : ℕ → Set α}, ∑' (i : ℕ), μ (s i) ≠ ⊤ → μ (limsup s atTop) = 0 :=
  @_root_.MeasureTheory.measure_limsup_atTop_eq_zero
