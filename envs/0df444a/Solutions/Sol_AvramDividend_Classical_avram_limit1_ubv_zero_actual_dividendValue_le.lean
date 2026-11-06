-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_ubv_zero_actual_dividendValue_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:02:15.184839+00:00
-- url     : https://prove2.me/submissions/ce81f502-0beb-4ec0-b3a2-bb61e6f47dbb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_smooth_differentiable
import Theorems.Thm_AvramDividend_Classical_verification_strategy_lump_sum_drop
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original UBV zero-reserve ruin law bounds the full admissible Stieltjes
    payout, preserving the right-payment atom at zero and every Iic endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D) :
    dividendValue X q 0 D ≤ ENNReal.ofReal (w 0) := by
  have hwSmooth' :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :=
    ⟨fun _ => hw_smooth, fun h => False.elim (hBV h)⟩
  have hwDiff :
      DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    local_verification_smooth_differentiable X w C hwSmooth'
  have hJump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X 0 D t ω) -
          w (riskProcess X 0 D t ω -
            (rightLimit D t ω - D t ω)) := by
    intro ω t ht
    exact verification_strategy_lump_sum_drop
      X w C hw_cont hwDiff hw_grad 0 (by simp) D hD ω t ht
  apply dividendValue_le_of_uniform_truncated_bounds
    X q 0 D hD.1 (ENNReal.ofReal (w 0))
  intro n
  exact avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
    X hBV q w C hw0 hw_cont hw_smooth hw_grad D hD hJump (n : ℝ) (by positivity)
