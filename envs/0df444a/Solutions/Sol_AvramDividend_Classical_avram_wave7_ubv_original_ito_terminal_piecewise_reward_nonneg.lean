-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:38:23.32881+00:00
-- url     : https://prove2.me/submissions/b5038cb5-eec7-45dd-8980-236e68d37064

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Discharge the exact original Ito-Meyer terminal reward sign premise,
    using the postpayment branch strictly before ruin and the ordinary
    reserve branch at ruin, with w(0)>=0 for creeping. -/
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
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω,
      Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ᵐ ω ∂P, 0 ≤ Term ω := by
  filter_upwards [] with ω
  rw [hTerm ω, hW ω]
  split_ifs with hpre
  · apply mul_nonneg (le_of_lt (Real.exp_pos _))
    exact avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
      X w C hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD ω (τ ω)
  · apply mul_nonneg (le_of_lt (Real.exp_pos _))
    exact avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative
      X w C hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD ω (τ ω)
end
