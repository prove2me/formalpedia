-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.integral_map_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:26:30.983686+00:00
-- url     : https://prove2.me/submissions/c2ac302e-4a9b-4fb9-be1f-a919da51d88d

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.integral_map_of_invariant
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
theorem solution (μ : Measure X) {q : X → X} (hq : Measurable q)
    {f : X → ℝ} (hf : AEStronglyMeasurable f (μ.map q)) (hinv : ∀ x, f (q x) = f x) :
    ∫ x, f x ∂(μ.map q) = ∫ x, f x ∂μ := by

  rw [integral_map hq.aemeasurable hf]
  simp only [hinv]