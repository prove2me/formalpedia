-- Prove2me | solution 3 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:37:25.755688+00:00
-- url     : https://prove2.me/submissions/8b45147c-5728-4e54-8dfc-7203645208c8

import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Reflecting at zero identifies the boundary strategy with the reflected-supremum value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  rw [barrierValue_self_eq_barrierSupValue X q 0]
  exact zero_reflectedSupValue_eq_barrierValue X hX q hq W hW
