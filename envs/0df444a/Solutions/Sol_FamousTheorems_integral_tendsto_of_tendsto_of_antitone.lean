-- Prove2me | solution 1 for FamousTheorems.integral_tendsto_of_tendsto_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:12:48.187066+00:00
-- url     : https://prove2.me/submissions/51915dd9-8a75-4fac-89d6-3250943b8216

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {m : MeasurableSpace α} 
    {μ : MeasureTheory.Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}, 
    (∀ (n : ℕ), MeasureTheory.Integrable (f n) μ) → 
    MeasureTheory.Integrable F μ → 
    (∀ᵐ (x : α) ∂μ, Antitone fun n => f n x) → 
    (∀ᵐ (x : α) ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) → 
    Tendsto (fun n => ∫ (x : α), f n x ∂μ) atTop (𝓝 (∫ (x : α), F x ∂μ)) :=
  @_root_.MeasureTheory.integral_tendsto_of_tendsto_of_antitone
