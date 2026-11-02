-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_postpayment_candidate_strict_positive_atomless_preruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:41:25.667352+00:00
-- url     : https://prove2.me/submissions/d8d32855-e492-499e-a24e-4eb7a873f636

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_predictable_candidate_strict_positive_before_localiser
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_atomless_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞) (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
        0 < w (x + X.X t ω - rightLimit D t ω) := by
  have hp :=
    avram_wave5_ubv_original_predictable_candidate_strict_positive_before_localiser
      X hBV w C hw0 hw_cont hw_smooth hw_grad x D hD σ hσ μ
  have he :=
    avram_wave4_p2_original_postpayment_reserve_atomless_continuity
      X x D hD.1.1 μ
  filter_upwards [hp, he] with ω hpω heω
  filter_upwards [hpω, heω] with t hpt het
  intro ht
  rw [het ht.1]
  exact hpt ht
