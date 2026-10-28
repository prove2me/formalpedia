-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_coe_toNNReal_with_measure_import
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:59:42.150636+00:00
-- url     : https://prove2.me/submissions/ce4cce1e-406a-4e0f-a110-60c4b3e10236

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) (ω : Ω) :
    (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
      min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞) := by 
  exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
