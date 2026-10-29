-- Prove2me | solution 2 for AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:24:06.938987+00:00
-- url     : https://prove2.me/submissions/48f7238d-98b3-4187-b648-971b30b60719

import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_standing_bounded_variation
import Theorems.Thm_AvramDividend_Classical_zero_barrier_instant_ruin_of_standing_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_instant_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Both Lévy variation classes satisfy the exact zero-reflection value
identity, using instantaneous ruin in the unbounded-variation case. -/
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
