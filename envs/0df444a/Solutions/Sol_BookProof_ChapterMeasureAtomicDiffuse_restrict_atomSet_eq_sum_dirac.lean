-- Prove2me | solution 1 for BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:57:30.668882+00:00
-- url     : https://prove2.me/submissions/9209505e-3c09-45a4-b743-9dd42e84f496

-- Generated from ChapterMeasureAtomicDiffuse.lean — solution of BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_countable_atomSet
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_restrict_eq_sum_dirac
open BookProof.ChapterMeasureAtomicDiffuse



noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

set_option maxHeartbeats 1000000 in
theorem solution [IsFiniteMeasure mu] :
    mu.restrict (atomSet mu)
      = Measure.sum (fun x : atomSet mu => mu {(x : α)} • Measure.dirac (x : α)) := restrict_eq_sum_dirac mu (countable_atomSet mu)
