-- Prove2me | solution 2 for AvramDividend.Classical.zero_reflectedSupValue_of_standing_bounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:28:18.517472+00:00
-- url     : https://prove2.me/submissions/a1dd7470-954d-451d-9e9f-8b7421018dff

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_bv_finite_activity
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_bv_infinite_activity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  by_cases hFinite : X.ν (Iio (0 : ℝ)) < ⊤
  · exact zero_reflectedSupValue_bv_finite_activity X hX q hq W hW hBV hFinite
  · exact zero_reflectedSupValue_bv_infinite_activity X hX q hq W hW hBV hFinite
