-- Prove2me | solution 1 for BookProof.ChapterSelectingEvents.singleton_null_in_continuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:30:51.348622+00:00
-- url     : https://prove2.me/submissions/f48cd016-f86f-4c69-acec-e78ca69f9fc8

-- Generated from ChapterSelectingEvents.lean — solution of BookProof.ChapterSelectingEvents.singleton_null_in_continuous
import Mathlib
import Definitions.Def_ChapterSelectingEvents
open BookProof.ChapterSelectingEvents



open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [NullSingletonClass μ] (x : α) : μ {x} = 0 := NullSingletonClass.measure_singleton x
