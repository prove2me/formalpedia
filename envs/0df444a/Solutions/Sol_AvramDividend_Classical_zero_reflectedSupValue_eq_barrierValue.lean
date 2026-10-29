-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:58:29.285241+00:00
-- url     : https://prove2.me/submissions/70a2bf11-ac08-485e-b855-13965c16c04d

import Theorems.Thm_AvramDividend_Classical_zero_barrier_instant_ruin_of_standing_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_standing_bounded_variation
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_instant_ruin
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Separate the zero-barrier identity into the genuine bounded-variation
    valuation and the unbounded-variation regularity hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  by_cases hBV : X.BoundedVariation
  · exact zero_reflectedSupValue_of_standing_bounded_variation
      X hX q hq W hW hBV
  · exact zero_reflectedSupValue_of_unbounded_instant_ruin
      X q hq W hW hBV
      (zero_barrier_instant_ruin_of_standing_unbounded_variation X hX hBV)
