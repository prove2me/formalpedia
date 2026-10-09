-- Prove2me | solution 1 for BookProof.ChapterG.evolution_conserves_probability
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:19:26.453722+00:00
-- url     : https://prove2.me/submissions/4d7939a5-1551-4f9f-afaa-44f6f9b865fe

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.evolution_conserves_probability
import Mathlib
import Definitions.Def_ChapterG
open MeasureTheory
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]
variable {A : Type*} [Ring A]

set_option maxHeartbeats 1000000 in
theorem solution {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T) :
    IsProbabilityMeasure (μ.map T) := MeasureTheory.Measure.isProbabilityMeasure_map hT.aemeasurable
