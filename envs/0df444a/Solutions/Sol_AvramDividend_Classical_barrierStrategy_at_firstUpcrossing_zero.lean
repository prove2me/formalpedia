-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_at_firstUpcrossing_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:59:36.334021+00:00
-- url     : https://prove2.me/submissions/2eae59e8-158d-4b0b-8889-f2865436e865

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_at_firstUpcrossing
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At the finite first record crossing, the barrier regulator has paid nothing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    barrierStrategy X x a u ω = 0 := by
  exact barrierStrategy_zero_at_firstUpcrossing X x a hxa ω u hu
