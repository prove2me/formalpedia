-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_of_standing_bounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:04:36.140491+00:00
-- url     : https://prove2.me/submissions/3cd2bbdd-f492-4978-9787-d86cb0a72f81

import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_bv_finite_activity
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_bv_infinite_activity
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
  · exact zero_reflectedSupValue_bv_finite_activity
      X hX q hq W hW hBV hFinite
  · exact zero_reflectedSupValue_bv_infinite_activity
      X hX q hq W hW hBV hFinite
