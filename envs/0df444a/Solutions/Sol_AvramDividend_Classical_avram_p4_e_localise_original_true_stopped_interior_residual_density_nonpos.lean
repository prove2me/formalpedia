-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_true_stopped_interior_residual_density_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:26:29.810974+00:00
-- url     : https://prove2.me/submissions/805498f9-7a09-4e2c-86d6-bf80822e4fa5

import Mathlib.Data.ENNReal.Basic
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
/-- Source UBV interior HJB density holds almost everywhere before the actual ruin-dominated clock. -/
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
    (hF : ∀ y : ℝ, 0 < y → y < c → F y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      0 < t → (t : ℝ≥0∞) < τ ω →
      F (riskProcess X x D t ω) ≤ 0 := by
  have hZero :=
    avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
      X hBV x (ENNReal.ofReal c) D hD τ hτ μ
  have hUpper :=
    avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
      X hBV x c D hDiv μ hCap
  filter_upwards [hZero, hUpper] with ω hZeroω hUpperω
  filter_upwards [hZeroω, hUpperω] with t ht0 htc
  intro ht hBefore
  have hBeforeRuin : (t : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_lt_of_le hBefore (hτ ω)
  exact hF _ (ht0 hBefore) (htc ⟨ht, hBeforeRuin⟩)
