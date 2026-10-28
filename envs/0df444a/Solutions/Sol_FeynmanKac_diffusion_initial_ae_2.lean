-- Prove2me | solution 2 for FeynmanKac.diffusion_initial_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:58:21.23791+00:00
-- url     : https://prove2.me/submissions/3673bf8d-2d22-4cee-8b1f-18991621f1e2

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence
import Theorems.Thm_LevyStochCalc_Brownian_Ito_version_ae_eq_zero_readable

open MeasureTheory
open LevyStochCalc.Brownian
open LevyStochCalc.Brownian.Multidim
open FunctionalInequalities.Probability.Diffusion

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {N d : ℕ} {W : MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
    {b : (Fin N → ℝ) → Fin N → ℝ}
    {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ}
    {x₀ : Fin N → ℝ} {Y : ℝ → Ω → Fin N → ℝ}
    (h : IsDiffusion W ℱ hW b σ x₀ Y) :
    (fun ω => Y 0 ω) =ᵐ[P] (fun _ => x₀) := by
  obtain ⟨hm, hp, hq, hX⟩ := h
  exact Ito.version_ae_eq_zero_readable W ℱ hW hX
