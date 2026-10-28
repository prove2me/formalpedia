-- Prove2me | solution 1 for AvramDividend.Classical.negative_measure_magnitude_pushforward_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:47:38.299523+00:00
-- url     : https://prove2.me/submissions/9381e174-72bf-4e59-97fd-4b0e14b8f7ff

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.NNReal.Defs
open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution (ν : Measure ℝ)
    (hneg : ν (Ici (0 : ℝ)) = 0) (hν : ν ≠ 0)
    (hf : Measurable (fun y : ℝ => Real.toNNReal (-y))) :
    0 < (ν.map (fun y : ℝ => Real.toNNReal (-y))) (Ioi (0 : ℝ≥0)) := by
  rw [Measure.map_apply hf measurableSet_Ioi]
  have hpre : (fun y : ℝ => Real.toNNReal (-y)) ⁻¹' Ioi (0 : ℝ≥0) = Iio 0 := by
    ext y; simp
  rw [hpre, pos_iff_ne_zero]
  intro h
  apply hν
  rw [← Measure.measure_univ_eq_zero]
  refine le_antisymm ?_ (zero_le (a := ν univ))
  calc ν univ ≤ ν (Iio 0 ∪ Ici 0) := by rw [Iio_union_Ici]
    _ ≤ ν (Iio 0) + ν (Ici 0) := measure_union_le _ _
    _ = 0 := by rw [h, hneg, add_zero]
