-- Prove2me | solution 3 for AvramDividend.Classical.barrier_zero_boundary_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:15:47.283979+00:00
-- url     : https://prove2.me/submissions/ccfabf15-9751-44a9-b710-ebd5fae15bbe

import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At reserve zero the barrier dividends coincide with stopped running-supremum
dividends, so the boundary value follows from the excursion identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  calc
    dividendValue X q 0 (barrierStrategy X 0 0) =
        barrierSupValue X 0 q :=
      barrierValue_self_eq_barrierSupValue X q 0
    _ = ENNReal.ofReal (barrierValue W 0 0) :=
      zero_reflectedSupValue_eq_barrierValue X hX q hq W hW
