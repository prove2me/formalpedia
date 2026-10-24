-- Prove2me | solution 1 for AvramDividend.Classical.chat04_exit_ratio_iff_stopped_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:06:48.537009+00:00
-- url     : https://prove2.me/submissions/2764cd35-d211-4c1b-9c21-6d3993c045c7

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The strict two-sided exit scale ratio and the stopped-scale balance
are algebraically equivalent whenever the upper scale is positive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a)) ↔
      (twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hden0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hdenTop : ENNReal.ofReal (W a) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  constructor
  · intro hRatio
    rw [hRatio, ENNReal.ofReal_div_of_pos hWa]
    exact ENNReal.div_mul_cancel hden0 hdenTop
  · intro hBalance
    exact chat04_exit_ratio_of_stopped_balance
      X hX q hq W hW a x ha hx0 hxa hBalance
