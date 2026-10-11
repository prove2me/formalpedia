-- Prove2me | solution 1 for BookProof.ChapterProbabilityInterface.transportMeasure_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:55.594485+00:00
-- url     : https://prove2.me/submissions/681d3009-9947-46c3-973c-8d6039eb0bca

-- Generated from ChapterProbabilityInterface.lean — solution of BookProof.ChapterProbabilityInterface.transportMeasure_isProbability
import Mathlib
import Definitions.Def_ChapterProbabilityInterface
open BookProof.ChapterProbabilityInterface



open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (transportMeasure e μ) := by

  exact Measure.isProbabilityMeasure_map e.measurable.aemeasurable
