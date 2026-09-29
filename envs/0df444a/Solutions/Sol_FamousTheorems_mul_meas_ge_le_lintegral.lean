-- Prove2me | solution 1 for FamousTheorems.mul_meas_ge_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:33.830077+00:00
-- url     : https://prove2.me/submissions/04b5e0f5-ba47-4d41-ad26-faeb621dd658

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
    {f : α → ENNReal}, Measurable f → ∀ (ε : ENNReal), ε * μ {x | ε ≤ f x} ≤ ∫⁻ (a : α), f a ∂μ :=
  @_root_.MeasureTheory.mul_meas_ge_le_lintegral
