-- Prove2me | solution 1 for BookProof.ChapterProbabilityInterface.translated_event_probability
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:56.509109+00:00
-- url     : https://prove2.me/submissions/3e7066e1-846c-4b5a-ab37-5f8af5c80666

-- Generated from ChapterProbabilityInterface.lean — solution of BookProof.ChapterProbabilityInterface.translated_event_probability
import Mathlib
import Definitions.Def_ChapterProbabilityInterface
open BookProof.ChapterProbabilityInterface



open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X)
    (s : Set Y) (hs : MeasurableSet s) :
    transportMeasure e μ s = μ (e ⁻¹' s) := by

  rw [transportMeasure, MeasureTheory.Measure.map_apply e.measurable hs]
