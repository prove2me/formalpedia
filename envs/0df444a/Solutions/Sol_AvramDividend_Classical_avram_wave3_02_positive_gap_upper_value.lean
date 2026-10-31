-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_positive_gap_upper_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:24:22.93063+00:00
-- url     : https://prove2.me/submissions/641656b0-6fab-4ebb-b952-f99a30377249

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_stoppedFirstRecord_upper_geometric_budgets
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_killed_grid_step

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An actual killed reflected reward admits a finite right-difference bound
at any positive record mesh with a strict scale increment, without derivatives. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε)) :
    barrierSupValue X a q ≤
      ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by
  obtain ⟨w, hw, hbudget, hstep⟩ :=
    stoppedFirstRecord_upper_geometric_budgets
      X hX q hq W hW a ε ha hε hWright hWa hWinc
  apply barrierSupValue_le_right_scale_quotient_of_killed_grid_step
    X W a 0 q ε hq.le hε hWright hWa hWinc w
  · intro n ω
    simpa only [zero_add] using hw n ω
  · exact hbudget
  · exact hstep
