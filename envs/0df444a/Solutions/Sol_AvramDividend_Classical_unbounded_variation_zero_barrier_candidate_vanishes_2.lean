-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:19:21.607469+00:00
-- url     : https://prove2.me/submissions/2ac5afb1-453d-4520-b5c3-d0a0fe782e29

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    barrierValue W 0 0 = 0 :=
  barrierValue_zero_of_scale_zero W
    (chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW)
