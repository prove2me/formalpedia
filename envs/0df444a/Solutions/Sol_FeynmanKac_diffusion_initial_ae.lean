-- Prove2me | solution 1 for FeynmanKac.diffusion_initial_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:56:40.380002+00:00
-- url     : https://prove2.me/submissions/5f4c6ba1-1379-4c40-a43d-db04f4860b6a

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence
import Theorems.Thm_LevyStochCalc_Brownian_Ito_version_ae_eq_zero_readable
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory
open LevyStochCalc.Brownian
open LevyStochCalc.Brownian.Multidim
open FunctionalInequalities.Probability.Diffusion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Every IsDiffusion process equals its deterministic starting vector at
elapsed time zero, outside a null set. -/
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
  rcases h with ⟨_, _, _, hv⟩
  simpa using
    (LevyStochCalc.Brownian.Ito.version_ae_eq_zero_readable W ℱ hW hv)
