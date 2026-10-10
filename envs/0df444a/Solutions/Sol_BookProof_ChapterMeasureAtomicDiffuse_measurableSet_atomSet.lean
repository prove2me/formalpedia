-- Prove2me | solution 1 for BookProof.ChapterMeasureAtomicDiffuse.measurableSet_atomSet
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:56:57.484979+00:00
-- url     : https://prove2.me/submissions/7e9c431a-b5f7-4dc0-952b-bc242ece33c7

-- Generated from ChapterMeasureAtomicDiffuse.lean — solution of BookProof.ChapterMeasureAtomicDiffuse.measurableSet_atomSet
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_countable_atomSet
open BookProof.ChapterMeasureAtomicDiffuse



noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

set_option maxHeartbeats 1000000 in
theorem solution [IsFiniteMeasure mu] : MeasurableSet (atomSet mu) := (countable_atomSet mu).measurableSet
