-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:26:43.845835+00:00
-- url     : https://prove2.me/submissions/558936d7-c973-49c0-8626-8c2b0f37fc11

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.physical_invariant_along_gaugeProjection
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
theorem solution {G : Type*} [Group G] [MulAction G X]
    {f : X → ℝ} (hf : IsPhysicalObservable G f) {q : X → X}
    (hq : ∀ x, ∃ g : G, q x = g • x) (x : X) : f (q x) = f x := by

  obtain ⟨g, hg⟩ := hq x
  rw [hg, hf g x]
