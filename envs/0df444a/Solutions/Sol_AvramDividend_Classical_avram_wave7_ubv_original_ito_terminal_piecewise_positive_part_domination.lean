-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_ito_terminal_piecewise_positive_part_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:41:58.742222+00:00
-- url     : https://prove2.me/submissions/d624f78f-6266-41ed-90a7-8d99a9a175dd

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_allcap_terminal_positive_part_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_allcap_postpayment_positive_part_domination

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Strong original-source domination of the exact piecewise Ito stopped
    terminal reward by w, including both zero creeping and overshoot. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, max 0 (W ω) ≤ w (W ω) := by
  intro ω
  rw [hW ω]
  split_ifs with hpre
  · exact avram_wave6_ubv_original_allcap_postpayment_positive_part_domination
      X w C hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD ω (τ ω)
  · exact avram_wave6_ubv_original_allcap_terminal_positive_part_domination
      X w C hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD ω (τ ω)
end
