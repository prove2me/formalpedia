-- Prove2me | solution 7 for AvramDividend.Classical.local_verification_uniform_strategy_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:12:21.701677+00:00
-- url     : https://prove2.me/submissions/73206cd0-edec-46e2-a6c3-155e801e66e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_signed_horizon_real_perpetual_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_hjb_candidate_ge_capital
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hwParts := local_verification_hjb_implies_components X q w C hw_hjb
  have hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    exact ⟨(hwParts y hy hyC).1, (hwParts y hy hyC).2.1⟩
  have hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    exact (hwParts y hy hyC).2.2
  have hwValueNonneg : 0 ≤ w x :=
    le_trans (show 0 ≤ x from hx)
      (hjb_candidate_ge_capital X q w C hw_cont hw0
        hw_smooth hw_hjb x hx hxC)
  rcases em X.BoundedVariation with hBV | hUBV
  · have hwC1 := hw_smooth.2 hBV
    have hwNonneg : ∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω) := by
      intro ω t _ hBefore
      have hRange := capped_riskProcess_range_before_ruin_including_zero
        X x hx C hxC D hD ω t hBefore
      exact le_trans hRange.1
        (hjb_candidate_ge_capital X q w C hw_cont hw0
          hw_smooth hw_hjb (riskProcess X x D t ω)
          hRange.1 hRange.2)
    have hwJump :=
      avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
        X C hC w hw_cont hwC1 hwGrad x hxC D hD
    have hPerpetual :=
      avram_limit2_bv_signed_horizon_real_perpetual_bridge
        X hBV q (le_of_lt hq) w C hC hw_cont hw0 hw_neg
        hwC1 hwGrad x hx hxC D hD hwJump (w x) hwValueNonneg
        (by
          intro T hT hTpos
          exact avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
            X hX hBV q hq w C hC hw_cont hw0 hw_neg hwC1
            hwGen hwGrad x hx hxC D hD hwNonneg hwJump T hT hTpos)
    exact hPerpetual.2.1
  · apply dividendValue_le_of_uniform_truncated_bounds
      X q x D hD.1 (ENNReal.ofReal (w x))
    intro n
    exact admissible_cap_truncated_dividendValue_le_unbounded_variation
      X hX hUBV q hq w C hC hw_cont hw0 hw_neg
      (hw_smooth.1 hUBV) hw_hjb x hx hxC D hD (n : ℝ)
      (by positivity)
