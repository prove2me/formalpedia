-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_infinite_cap_stopped_integrable_drift_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:32:37.394715+00:00
-- url     : https://prove2.me/submissions/dcc3ee31-aed6-4d21-b3f2-6facba2aa077

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Every explicitly integrable original infinite-cap stopped drift has nonpositive integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x ⊤ D)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (F : ℝ → ℝ)
    (hF : ∀ y : ℝ, 0 < y → F y ≤ 0)
    (hIntegrable : ∀ ω, Integrable
      (fun t : ℝ≥0 => if (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0) μ) :
    ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0, if (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0 ∂μ) ≤ 0 := by
  have hPositive :=
    avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
      X hBV x (⊤ : ℝ≥0∞) D hD τ hτ μ
  filter_upwards [hPositive] with ω hω
  have hSign : ∀ᵐ t : ℝ≥0 ∂μ,
      (if (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0) ≤ 0 := by
    filter_upwards [hω] with t ht
    split_ifs with hBefore
    · exact hF _ (ht hBefore)
    · exact le_refl 0
  exact integral_nonpos_of_ae hSign
