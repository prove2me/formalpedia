-- Prove2me | solution 1 for BookProof.ChapterG3.integral_eventProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T13:30:58.289015+00:00
-- url     : https://prove2.me/submissions/a31d0fc9-b008-4919-a694-8721224183ef

-- Generated from ChapterG3.lean — solution of BookProof.ChapterG3.integral_eventProj
import Mathlib
import Definitions.Def_ChapterG3
import Definitions.Def_ChapterConservativeDiagonal
open BookProof.ChapterG3



open MeasureTheory
open scoped ENNReal
open BookProof.ConservativeDiagonal



variable {X : Type*}

variable {X : Type*}

set_option maxHeartbeats 1000000 in
theorem solution [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (A : Set X) (hA : MeasurableSet A) :
    ∫ x, BookProof.ChapterG3.eventProj A x ∂μ = (μ A).toReal := by

  rw [BookProof.ChapterG3.eventProj, MeasureTheory.integral_indicator_one hA, MeasureTheory.measureReal_def]
