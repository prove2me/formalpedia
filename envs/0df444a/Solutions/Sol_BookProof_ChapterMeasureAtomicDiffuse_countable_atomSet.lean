-- Prove2me | solution 1 for BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:56:22.563931+00:00
-- url     : https://prove2.me/submissions/3ce7e1cb-9b05-4e09-936d-37c659745f91

-- Generated from ChapterMeasureAtomicDiffuse.lean — solution of BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse



noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

set_option maxHeartbeats 1000000 in
theorem solution [IsFiniteMeasure mu] : (atomSet mu).Countable := by

  have h := Measure.countable_meas_pos_of_disjoint_iUnion (μ := mu)
    (As := fun x : α => ({x} : Set α)) (fun x => measurableSet_singleton x)
    (by intro i j hij; simpa [Function.onFun] using hij)
  simpa [atomSet, pos_iff_ne_zero] using h
