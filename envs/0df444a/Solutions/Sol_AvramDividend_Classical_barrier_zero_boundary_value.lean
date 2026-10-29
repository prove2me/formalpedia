-- Prove2me | solution 1 for AvramDividend.Classical.barrier_zero_boundary_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:17:22.787677+00:00
-- url     : https://prove2.me/submissions/6791f549-11a7-4e46-a370-6695f70cd3da

import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue
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
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  calc
    dividendValue X q 0 (barrierStrategy X 0 0) =
        barrierSupValue X 0 q := barrierValue_self_eq_barrierSupValue X q 0
    _ = ENNReal.ofReal (barrierValue W 0 0) :=
      zero_reflectedSupValue_eq_barrierValue X hX q hq W hW
