-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_named_ratio_to_named_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:46:27.481239+00:00
-- url     : https://prove2.me/submissions/f987a6d8-5813-4fbf-9afb-3776315df47b

import Mathlib.Data.ENNReal.Inv
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Source-faithful converse ratio normalisation: strict positivity of
the Standing q-scale denominator permits ENNReal cancellation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hRatio : twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a)) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hden0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hdenTop : ENNReal.ofReal (W a) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  calc
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a) := by
          rw [hRatio]
    _ = (ENNReal.ofReal (W x) / ENNReal.ofReal (W a)) *
        ENNReal.ofReal (W a) := by
          rw [ENNReal.ofReal_div_of_pos hWa]
    _ = ENNReal.ofReal (W x) :=
        ENNReal.div_mul_cancel hden0 hdenTop
