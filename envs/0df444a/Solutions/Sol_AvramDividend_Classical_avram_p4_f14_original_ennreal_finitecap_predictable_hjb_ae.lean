-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f14_original_ennreal_finitecap_predictable_hjb_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:46:20.882207+00:00
-- url     : https://prove2.me/submissions/53378d74-e0ba-4560-bf51-d3294c148613

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_admissible_finitecap_predictable_hjb_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞) (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
      let y : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      (0 < y ∧ ENNReal.ofReal y < C) ∧
        ContDiffWithinAt ℝ 2 w
          {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} y ∧
        X.GeneratorIntegrable w y ∧
        X.generator w y - q * w y ≤ 0 ∧ 1 ≤ deriv w y := by
  have hCap : ENNReal.ofReal C.toReal = C :=
    ENNReal.ofReal_toReal hFinite
  have hc : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFinite
  have hSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal C.toReal} := by
    simpa only [hCap] using hw_smooth
  have hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal C.toReal →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    simpa only [hCap] using hw_gen
  have hGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal C.toReal →
      1 ≤ deriv w y := by
    simpa only [hCap] using hw_grad
  have hxc' : ENNReal.ofReal x ≤ ENNReal.ofReal C.toReal := by
    simpa only [hCap] using hxc
  have hD' : IsAdmissibleLe X x (ENNReal.ofReal C.toReal) D := by
    simpa only [hCap] using hD
  have hResult :=
    avram_wave7_18_original_admissible_finitecap_predictable_hjb_ae
      X hBV q C.toReal hc w hSmooth hGen hGrad x hx hxc' D hD' σ hσ μ
  simpa only [hCap] using hResult
