-- Prove2me | solution 1 for FamousTheorems.lintegral_mul_le_lp_mul_lq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:17.396478+00:00
-- url     : https://prove2.me/submissions/270eb4bd-0ba6-4044-997e-1c4f663b3903

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
    {p q : ℝ}, 
    p.HolderConjugate q → 
    ∀ {f g : α → NNReal}, 
    AEMeasurable f μ → 
    AEMeasurable g μ → 
    ∫⁻ (a : α), ↑((f * g) a) ∂μ ≤ (∫⁻ (a : α), ↑(f a) ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), ↑(g a) ^ q ∂μ) ^ (1 / q) :=
  @_root_.NNReal.lintegral_mul_le_Lp_mul_Lq
