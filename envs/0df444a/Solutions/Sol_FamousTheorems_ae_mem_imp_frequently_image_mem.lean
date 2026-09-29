-- Prove2me | solution 1 for FamousTheorems.ae_mem_imp_frequently_image_mem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:11.839749+00:00
-- url     : https://prove2.me/submissions/e8bf5bb5-7ac1-49de-98f0-4e9ffd135702

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {f : α → α} 
    {s : Set α} {μ : MeasureTheory.Measure α}, 
    MeasureTheory.Conservative f μ → 
    MeasureTheory.NullMeasurableSet s μ → ∀ᵐ (x : α) ∂μ, x ∈ s → ∃ᶠ (n : ℕ) in atTop, f^[n] x ∈ s :=
  @_root_.MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem
