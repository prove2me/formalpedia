-- Prove2me | solution 1 for FamousTheorems.levy_upward_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:55:26.776856+00:00
-- url     : https://prove2.me/submissions/ec09e73b-2641-44a7-9099-56b3f82a9207

import Mathlib

open MeasureTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0} [IsFiniteMeasure μ]
    (g : Ω → ℝ) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun n => μ[g | ℱ n] x) Filter.atTop (nhds (μ[g | ⨆ n, ℱ n] x)) :=
  tendsto_ae_condExp g
