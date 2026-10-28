-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:18:09.639787+00:00
-- url     : https://prove2.me/submissions/b5e24e43-79e4-45a1-8b58-675549d292ed

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The zero-barrier scale-function candidate vanishes for unbounded
variation, without a derivative or standing-assumption hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    barrierValue W 0 0 = 0 := by
  exact barrierValue_zero_of_scale_zero W
    (chat04_scale_zero_origin_of_unbounded_variation
      X hnbv q hq W hW)
