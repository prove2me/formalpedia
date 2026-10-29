-- Prove2me | solution 1 for AvramDividend.Classical.bv_capped_raw_lower_clock_NNReal_measurable_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:19:17.142229+00:00
-- url     : https://prove2.me/submissions/f796020d-3bc1-44a7-a150-d2f56c90cfca

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_raw_lower_clock_measurable_ws01c
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (lower : ℝ) (T : ℝ≥0) :
    Measurable (fun ω : Ω =>
      (twoSidedExitDownTime X lower ω ⊓ (T : ℝ≥0∞)).toNNReal) :=
  ENNReal.measurable_toNNReal.comp
    ((bv_raw_lower_clock_measurable_ws01c X lower).inf measurable_const)
