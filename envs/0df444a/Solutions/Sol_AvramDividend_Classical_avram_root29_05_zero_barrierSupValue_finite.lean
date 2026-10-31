-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_zero_barrierSupValue_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:24:08.018215+00:00
-- url     : https://prove2.me/submissions/e5283ba8-b042-4463-8d3f-a9ffac5276a6

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The actual killed Stieltjes dividend value at a zero barrier is finite
under the established genuine zero-reflection identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    barrierSupValue X 0 q < ∞ := by
  rw [zero_reflectedSupValue_eq_barrierValue X hX q hq W hW]
  exact ENNReal.ofReal_lt_top
