-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_postpayment_positive_part_lintegral_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:34:36.601595+00:00
-- url     : https://prove2.me/submissions/30fbfedd-18cb-42c1-b187-d6f47c916866

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_allcap_postpayment_positive_part_domination

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Discounted postpayment terminal positive-part expected domination
    under any finitely clipped source stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0∞) (hτstop : IsStoppingTime 𝓕.rightCont τ)
    (T : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (
        Real.exp (-q * ((min (τ ω) (T : ℝ≥0∞)).toNNReal : ℝ)) *
        max 0 (x + X.X (min (τ ω) (T : ℝ≥0∞)).toNNReal ω -
          rightLimit D (min (τ ω) (T : ℝ≥0∞)).toNNReal ω)) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (
        Real.exp (-q * ((min (τ ω) (T : ℝ≥0∞)).toNNReal : ℝ)) *
        w (x + X.X (min (τ ω) (T : ℝ≥0∞)).toNNReal ω -
          rightLimit D (min (τ ω) (T : ℝ≥0∞)).toNNReal ω)) ∂P) := by
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left
  · exact avram_wave6_ubv_original_allcap_postpayment_positive_part_domination
      X w C hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD ω (min (τ ω) (T : ℝ≥0∞)).toNNReal
  · exact le_of_lt (Real.exp_pos _)
end
