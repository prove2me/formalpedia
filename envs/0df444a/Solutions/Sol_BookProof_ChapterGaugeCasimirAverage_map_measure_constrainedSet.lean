-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:26:30.109989+00:00
-- url     : https://prove2.me/submissions/71ef0072-e29f-4eb5-a601-bd8a09a9f112

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.map_measure_constrainedSet
import Mathlib
import Definitions.Def_ChapterGaugeCasimirAverage
open BookProof.ChapterGaugeCasimirAverage




open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]
variable {X : Type*}
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable {X : Type*} {G : Type*} [Group G] [MulAction G X]
variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure X) [IsProbabilityMeasure μ]
    {C : Set X} (hC : MeasurableSet C) {q : X → X} (hq : Measurable q)
    (hqC : ∀ x, q x ∈ C) : (μ.map q) C = 1 := by

  have hpre : q ⁻¹' C = Set.univ := Set.eq_univ_of_forall hqC
  rw [Measure.map_apply hq hC, hpre, measure_univ]
