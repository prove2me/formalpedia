-- Prove2me | solution 3 for AvramDividend.Classical.zero_reflectedSupValue_of_standing_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:22:55.305546+00:00
-- url     : https://prove2.me/submissions/27e45663-8e76-4958-b2c0-bad836b3c72c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_bv_finite_activity
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_bv_infinite_activity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite and infinite negative-jump activity exhaust the bounded-variation
Lévy case and supply the same canonical reflected value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  by_cases hFinite : X.ν (Iio (0 : ℝ)) < ⊤
  · exact zero_reflectedSupValue_bv_finite_activity
      X hX q hq W hW hBV hFinite
  · exact zero_reflectedSupValue_bv_infinite_activity
      X hX q hq W hW hBV hFinite
