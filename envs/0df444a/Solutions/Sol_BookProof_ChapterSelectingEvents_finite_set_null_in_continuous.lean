-- Prove2me | solution 1 for BookProof.ChapterSelectingEvents.finite_set_null_in_continuous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:30:52.23702+00:00
-- url     : https://prove2.me/submissions/0d7748ce-3d80-470e-8124-2bc125a58f7e

-- Generated from ChapterSelectingEvents.lean — solution of BookProof.ChapterSelectingEvents.finite_set_null_in_continuous
import Mathlib
import Definitions.Def_ChapterSelectingEvents
open BookProof.ChapterSelectingEvents



open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [NullSingletonClass μ] (s : Finset α) : μ (s : Set α) = 0 := Finset.measure_zero s μ
