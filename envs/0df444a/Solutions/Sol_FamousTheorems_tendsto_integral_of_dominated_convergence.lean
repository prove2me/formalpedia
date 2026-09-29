-- Prove2me | solution 1 for FamousTheorems.tendsto_integral_of_dominated_convergence
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:08.967559+00:00
-- url     : https://prove2.me/submissions/e1fabbfb-a2f1-453b-8265-8bf21567a126

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] 
    [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {F : ℕ → α → G} {f : α → G} 
    (bound : α → ℝ), 
    (∀ (n : ℕ), MeasureTheory.AEStronglyMeasurable (F n) μ) → 
    MeasureTheory.Integrable bound μ → 
    (∀ (n : ℕ), ∀ᵐ (a : α) ∂μ, ‖F n a‖ ≤ bound a) → 
    (∀ᵐ (a : α) ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) → 
    Tendsto (fun n => ∫ (a : α), F n a ∂μ) atTop (𝓝 (∫ (a : α), f a ∂μ)) :=
  @_root_.MeasureTheory.tendsto_integral_of_dominated_convergence
