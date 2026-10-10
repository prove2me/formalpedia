-- Prove2me | solution 1 for BookProof.ChapterMAPNull.countable_map_set_measure_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:28:17.309016+00:00
-- url     : https://prove2.me/submissions/16b22d2b-5286-438f-8b2a-6aedd502f12c

-- Generated from ChapterMAPNull.lean — solution of BookProof.ChapterMAPNull.countable_map_set_measure_zero
import Mathlib
import Definitions.Def_ChapterMAPNull
open BookProof.ChapterMAPNull



open MeasureTheory


variable {α : Type*} [MeasurableSpace α]

variable {α : Type*} [MeasurableSpace α]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure α) [NullSingletonClass μ]
    (maximizers : Set α) (hcountable : maximizers.Countable) :
    μ maximizers = 0 := by

  exact hcountable.measure_zero μ
