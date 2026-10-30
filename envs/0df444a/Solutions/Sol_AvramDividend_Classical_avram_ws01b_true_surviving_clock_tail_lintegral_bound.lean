-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_true_surviving_clock_tail_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:02:18.144038+00:00
-- url     : https://prove2.me/submissions/b903004e-a348-47d8-9248-22265be97924

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_surviving_horizon_reserve_strip
import Theorems.Thm_AvramDividend_Classical_chat04_survived_strip_scale_tail_lintegral_bound

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (T : ℝ≥0) :
    (∫⁻ ω, if (T : ℝ≥0∞) < twoSidedExitUpTime X (a-x) ω ∧
                (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
       ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))
      else 0 ∂P) ≤
    ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W a) := by
  refine le_trans (lintegral_mono fun ω => ?_) (chat04_survived_strip_scale_tail_lintegral_bound X q hq W hW a x T T le_rfl)
  by_cases h : (T : ℝ≥0∞) < twoSidedExitUpTime X (a-x) ω ∧ (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω
  · rw [if_pos h, if_pos (avram_ws01b_true_surviving_horizon_reserve_strip X a x T ω h.1 h.2)]
  · rw [if_neg h]; exact bot_le
