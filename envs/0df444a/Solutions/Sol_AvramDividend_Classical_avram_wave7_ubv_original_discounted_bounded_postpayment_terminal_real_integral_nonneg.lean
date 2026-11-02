-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_postpayment_terminal_real_integral_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:28:00.604971+00:00
-- url     : https://prove2.me/submissions/94032dd6-e0e0-4971-a9d2-cc54e8825936

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Original UBV discounted postpayment terminal positivity under any
    finite clipping of a genuine source stopping clock. -/
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
    0 ≤ (∫ ω, Real.exp (-q * ((min (τ ω) (T : ℝ≥0∞)).toNNReal : ℝ)) *
      w (x + X.X (min (τ ω) (T : ℝ≥0∞)).toNNReal ω -
        rightLimit D (min (τ ω) (T : ℝ≥0∞)).toNNReal ω) ∂P) := by
  apply integral_nonneg_of_ae
  filter_upwards [] with ω
  apply mul_nonneg (le_of_lt (Real.exp_pos _))
  exact avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
    X w C hw0 hw_cont hw_neg hw_smooth hw_grad
    x hxc D hD ω (min (τ ω) (T : ℝ≥0∞)).toNNReal
end
