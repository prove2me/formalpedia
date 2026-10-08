-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_eq_thresholded_self_below_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T07:19:05.374078+00:00
-- url     : https://prove2.me/submissions/4f085648-57d6-4378-b38c-5ceb8e4d82dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_offset_of_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hxa : x ≤ a) :
    barrierStrategy X x a =
      (fun t ω => max 0 (barrierStrategy X a a t ω - (a - x))) := by
  funext t ω
  exact barrierStrategy_offset_of_le X x a hxa t ω
