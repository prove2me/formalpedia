-- Prove2me | solution 5 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:54:04.571286+00:00
-- url     : https://prove2.me/submissions/9da21e9f-ab8a-4bcc-ab85-598cddb33a78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The pathwise reflection identity reduces the zero-barrier dividend value
to the stopped-supremum scale boundary identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  calc
    dividendValue X q 0 (barrierStrategy X 0 0) =
        barrierSupValue X 0 q :=
      barrierValue_self_eq_barrierSupValue X q 0
    _ = ENNReal.ofReal (barrierValue W 0 0) :=
      zero_reflectedSupValue_eq_barrierValue X hX q hq W hW
