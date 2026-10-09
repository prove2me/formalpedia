-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.gaugeAverage_isPhysicalObservable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:25:11.804169+00:00
-- url     : https://prove2.me/submissions/d4a711a7-785d-4b7b-8149-e2d743ebd878

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.gaugeAverage_isPhysicalObservable
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
theorem solution (μ : Measure G) [μ.IsMulRightInvariant]
    (f : X → ℝ) : IsPhysicalObservable G (gaugeAverage (X := X) μ f) := by

  intro h x
  have hmp : MeasurePreserving (fun g : G => g * h) μ μ := measurePreserving_mul_right μ h
  have hme : MeasurableEmbedding (fun g : G => g * h) :=
    (MeasurableEquiv.mulRight h).measurableEmbedding
  have hint := hmp.integral_comp hme (fun g : G => f (g • x))
  simpa [gaugeAverage, mul_smul] using hint
