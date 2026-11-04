-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_infinite_cap_stopped_generator_integrable_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:35:04.232197+00:00
-- url     : https://prove2.me/submissions/8c9d631e-e767-4cfb-a09b-ba31cdeed2f5

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Infinite-cap same-source full generator integrability and HJB sign hold from zero occupation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x ⊤ D)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      (t : ℝ≥0∞) < τ ω →
      X.GeneratorIntegrable w (riskProcess X x D t ω) ∧
        X.generator w (riskProcess X x D t ω) -
        q * w (riskProcess X x D t ω) ≤ 0 := by
  have hZero :=
    avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
      X hBV x (⊤ : ℝ≥0∞) D hD τ hτ μ
  filter_upwards [hZero] with ω hZeroω
  filter_upwards [hZeroω] with t ht0
  intro hBefore
  exact hwGen _ (ht0 hBefore)
