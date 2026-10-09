-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.gaugeAverage_of_isPhysicalObservable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:25:25.807712+00:00
-- url     : https://prove2.me/submissions/89aa59b8-8489-4a08-b14e-38857ef4384a

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.gaugeAverage_of_isPhysicalObservable
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

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure G) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : IsPhysicalObservable G f) :
    gaugeAverage (X := X) μ f = f := by

  funext x
  simp [gaugeAverage, hf _ x]
