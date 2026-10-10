-- Prove2me | solution 1 for BookProof.ChapterMeasureAtomicDiffuse.mem_atomSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:55:26.674121+00:00
-- url     : https://prove2.me/submissions/496bc34d-29dc-41b1-89f3-41a52b494647

-- Generated from ChapterMeasureAtomicDiffuse.lean — solution of BookProof.ChapterMeasureAtomicDiffuse.mem_atomSet_iff
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse



noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

set_option maxHeartbeats 1000000 in
theorem solution (x : α) : x ∈ atomSet mu ↔ mu {x} ≠ 0 := Iff.rfl
