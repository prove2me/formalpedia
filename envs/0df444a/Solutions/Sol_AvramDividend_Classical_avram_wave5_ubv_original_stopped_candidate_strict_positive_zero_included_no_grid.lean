-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_stopped_candidate_strict_positive_zero_included_no_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:02:50.115397+00:00
-- url     : https://prove2.me/submissions/f9a7c1e2-11ec-4d0e-a697-14582990d45f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < σ ω →
        0 < w (riskProcess X x D t ω) := by
  have hres := avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
    X hBV x C D hD σ hσ μ
  filter_upwards [hres] with ω hω
  filter_upwards [hω] with t ht
  intro hpre
  have hy : 0 < riskProcess X x D t ω := ht hpre
  have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C :=
    admissibleLe_riskProcess_le_cap_all_times X x C D hD hxc ω t
  have hsec := avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
    C w hw_cont hw_smooth hw_grad 0 (riskProcess X x D t ω)
    (le_refl (0 : ℝ)) (le_of_lt hy) hcap
  linarith
