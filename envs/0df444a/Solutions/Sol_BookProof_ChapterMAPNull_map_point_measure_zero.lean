-- Prove2me | solution 1 for BookProof.ChapterMAPNull.map_point_measure_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:27:28.206887+00:00
-- url     : https://prove2.me/submissions/a87ce912-802c-4c4d-8c4e-54ffc0d1fea4

-- Generated from ChapterMAPNull.lean — solution of BookProof.ChapterMAPNull.map_point_measure_zero
import Mathlib
import Definitions.Def_ChapterMAPNull
open BookProof.ChapterMAPNull



open MeasureTheory


variable {α : Type*} [MeasurableSpace α]

variable {α : Type*} [MeasurableSpace α]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure α) [NullSingletonClass μ] (mapPoint : α) :
    μ {mapPoint} = 0 := by

  exact measure_singleton mapPoint
