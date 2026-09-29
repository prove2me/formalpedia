-- Prove2me | solution 1 for FamousTheorems.lintegral_iinf_ae
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:09.326508+00:00
-- url     : https://prove2.me/submissions/554a01a8-2244-461e-a63e-ec1ae35233d0

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
    {f : ℕ → α → ENNReal}, 
    (∀ (n : ℕ), Measurable (f n)) → 
    (∀ (n : ℕ), f n.succ ≤ᵐ[μ] f n) → ∫⁻ (a : α), f 0 a ∂μ ≠ ⊤ → ∫⁻ (a : α), ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ (a : α), f n a ∂μ :=
  @_root_.MeasureTheory.lintegral_iInf_ae
