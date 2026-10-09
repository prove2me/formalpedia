-- Prove2me | solution 1 for BookProof.ChapterG2.exists_haar_measure_for_gauge_group
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:22:33.903012+00:00
-- url     : https://prove2.me/submissions/117440e5-12e3-43ce-be83-54418223e1d2

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.exists_haar_measure_for_gauge_group
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

set_option maxHeartbeats 1000000 in
theorem solution (G : Type*)
    [MeasurableSpace G] [TopologicalSpace G] [LocallyCompactSpace G] [Group G]
    [BorelSpace G] [IsTopologicalGroup G] :
    ∃ (μ : Measure G), μ.IsHaarMeasure := by

  refine ⟨MeasureTheory.Measure.haar, ?_⟩
  infer_instance
