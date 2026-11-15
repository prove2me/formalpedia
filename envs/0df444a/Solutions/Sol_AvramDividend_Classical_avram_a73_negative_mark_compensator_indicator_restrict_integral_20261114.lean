-- Prove2me | solution 1 for AvramDividend.Classical.avram_a73_negative_mark_compensator_indicator_restrict_integral_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:16:03.258018+00:00
-- url     : https://prove2.me/submissions/24838ba6-9428-4ebd-8c69-bae09ea12036

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ) :
    (∫ y in Iio (0 : ℝ),
      y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂ν) =
    (∫ y in Ioo (-1 : ℝ) 0, y ∂ν) := by
  have hIndicator (y : ℝ) :
      (Iio (0 : ℝ)).indicator
        (fun y => y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) y =
      (Ioo (-1 : ℝ) 0).indicator (fun y => y) y := by
    by_cases hy0 : y < 0
    · by_cases hym : -1 < y
      · have hy1 : y < 1 := lt_trans hy0 (by norm_num)
        simp [Set.indicator, Set.mem_Ioo, Set.mem_Iio, hy0, hym, hy1]
      · simp [Set.indicator, Set.mem_Ioo, Set.mem_Iio, hy0, hym]
    · simp [Set.indicator, Set.mem_Ioo, Set.mem_Iio, hy0]
  calc
    (∫ y in Iio (0 : ℝ),
      y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y ∂ν) =
        ∫ y, (Iio (0 : ℝ)).indicator
          (fun y => y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) y ∂ν :=
        (integral_indicator measurableSet_Iio).symm
    _ = ∫ y, (Ioo (-1 : ℝ) 0).indicator (fun y => y) y ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact hIndicator y
    _ = ∫ y in Ioo (-1 : ℝ) 0, y ∂ν :=
      integral_indicator measurableSet_Ioo
