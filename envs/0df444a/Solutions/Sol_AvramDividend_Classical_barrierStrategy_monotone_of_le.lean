-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_monotone_of_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:30:57.708827+00:00
-- url     : https://prove2.me/submissions/754d8a14-8dec-487d-967c-6995f08c1a4a

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_offset_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The dividend regulator is monotone from any initial capital no greater than its barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a) (ω : Ω) :
    Monotone (fun t : ℝ≥0 => barrierStrategy X x a t ω) := by
  intro s t hst
  calc
    barrierStrategy X x a s ω =
        max 0 (barrierStrategy X a a s ω - (a - x)) :=
      barrierStrategy_offset_of_le X x a hxa s ω
    _ ≤ max 0 (barrierStrategy X a a t ω - (a - x)) :=
      max_le_max le_rfl
        (sub_le_sub_right ((barrierStrategy_monotone X a ω) hst) (a - x))
    _ = barrierStrategy X x a t ω :=
      (barrierStrategy_offset_of_le X x a hxa t ω).symm
