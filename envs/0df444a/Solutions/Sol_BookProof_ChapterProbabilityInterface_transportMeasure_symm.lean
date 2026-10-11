-- Prove2me | solution 1 for BookProof.ChapterProbabilityInterface.transportMeasure_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:07:45.781776+00:00
-- url     : https://prove2.me/submissions/3f247421-1c63-4ecc-93f2-41891b14e190

-- Generated from ChapterProbabilityInterface.lean — solution of BookProof.ChapterProbabilityInterface.transportMeasure_symm
import Mathlib
import Definitions.Def_ChapterProbabilityInterface
open BookProof.ChapterProbabilityInterface



open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X) :
    transportMeasure e.symm (transportMeasure e μ) = μ := by

  simp [transportMeasure]
