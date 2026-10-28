-- Prove2me | solution 1 for AvramDividend.Classical.chat12_total_expected_upper_scale_finite_of_exit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:37:07.474484+00:00
-- url     : https://prove2.me/submissions/a41a9353-1c0d-49da-ba4b-2bd91f4f8d6d

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_scale_closed_form_of_exit
import Theorems.Thm_AvramDividend_Classical_chat12_geometric_budget_lt_top_of_ratio_lt_one

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε))
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) :
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) < ∞ := by
  exact lt_of_le_of_lt
    (chat12_total_expected_upper_scale_closed_form_of_exit X hX q hq W hW a ε ha hε hWright hWa hWinc hExit)
    (chat12_geometric_budget_lt_top_of_ratio_lt_one ε (W a / W (a + ε)) hε.le
      (div_nonneg hWa hWright.le) ((div_lt_one hWright).mpr hWinc))
