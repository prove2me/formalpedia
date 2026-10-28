-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_clock_eq_true_clock_within_horizon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:17:22.25677+00:00
-- url     : https://prove2.me/submissions/c00c1930-4a17-46c2-9339-7c092cba7d82

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) (ω : Ω)
    (hN : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal =
      (twoSidedExitUpTime X b ω).toNNReal := by 
  rw [min_eq_left hN]
