-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_true_stopped_integrable_generator_density_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:26:31.446678+00:00
-- url     : https://prove2.me/submissions/7567b141-a7de-4340-8b61-84214dc23d3f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
/-- Stopped original generator drift has nonpositive physical-time integral, assuming explicit L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (F : ℝ → ℝ)
    (hF : ∀ y : ℝ, 0 < y → y < c → F y ≤ 0)
    (hIntegrable : ∀ ω, Integrable
      (fun t : ℝ≥0 => if 0 < t ∧ (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0) μ) :
    ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0 ∂μ) ≤ 0 := by
  have hZero :=
    avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
      X hBV x (ENNReal.ofReal c) D hD τ hτ μ
  have hUpper :=
    avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
      X hBV x c D hDiv μ hCap
  filter_upwards [hZero, hUpper] with ω hZeroω hUpperω
  have hDensity : ∀ᵐ t : ℝ≥0 ∂μ,
      (if 0 < t ∧ (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0) ≤ 0 := by
    filter_upwards [hZeroω, hUpperω] with t ht0 htc
    split_ifs with ht
    · have hRuin : (t : ℝ≥0∞) < ruinTime X x D ω :=
        lt_of_lt_of_le ht.2 (hτ ω)
      exact hF _ (ht0 ht.2) (htc ⟨ht.1, hRuin⟩)
    · exact le_refl 0
  exact integral_nonpos_of_ae hDensity
