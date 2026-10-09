-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.finiteGaugeAverage_isPhysicalObservable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:25:38.959989+00:00
-- url     : https://prove2.me/submissions/27fa9462-c345-47c7-a19b-f6b19ae96106

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.finiteGaugeAverage_isPhysicalObservable
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

set_option maxHeartbeats 1000000 in
theorem solution (f : X → ℝ) :
    IsPhysicalObservable G (finiteGaugeAverage (X := X) G f) := by

  intro h x
  have hsum : ∑ g : G, f ((g * h) • x) = ∑ g : G, f (g • x) :=
    Equiv.sum_comp (Equiv.mulRight h) (fun g : G => f (g • x))
  simp only [finiteGaugeAverage, mul_smul] at hsum ⊢
  rw [hsum]
