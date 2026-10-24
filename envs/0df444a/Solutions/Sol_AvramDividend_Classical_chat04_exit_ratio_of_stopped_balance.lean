-- Prove2me | solution 1 for AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:56:36.321574+00:00
-- url     : https://prove2.me/submissions/c3047e2a-f100-402d-8758-38bf87f47b76

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Algebraically normalise the strict two-sided exit balance by the
strictly positive scale function at the upper boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hBalance :
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hden0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hdenTop : ENNReal.ofReal (W a) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  calc
    twoSidedExitExpectation X q a x =
        (twoSidedExitExpectation X q a x * ENNReal.ofReal (W a)) /
          ENNReal.ofReal (W a) := by
      symm
      exact ENNReal.mul_div_cancel_right hden0 hdenTop
    _ = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
      rw [hBalance]
    _ = ENNReal.ofReal (W x / W a) := by
      exact (ENNReal.ofReal_div_of_pos hWa).symm
