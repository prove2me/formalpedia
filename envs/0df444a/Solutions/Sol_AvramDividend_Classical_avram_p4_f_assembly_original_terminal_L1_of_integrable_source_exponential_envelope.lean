-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_of_integrable_source_exponential_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:58:38.895012+00:00
-- url     : https://prove2.me/submissions/d3f06993-d1cb-4117-9197-df4afdcd669a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Conditional source envelope yields genuine stopped terminal L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (q θ K : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y))
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hRawI : Integrable (fun ω =>
      Real.exp (-(q * (τ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (τ ω) ω)))) P) :
    Integrable Term P := by
  have hUpper :=
    avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
      X C x D hD τ W Term hW w q θ K hθ hK hwGrowth hTerm
  exact hRawI.mono_nonneg hTermMeas hTermNonneg
    (Filter.Eventually.of_forall hUpper)
