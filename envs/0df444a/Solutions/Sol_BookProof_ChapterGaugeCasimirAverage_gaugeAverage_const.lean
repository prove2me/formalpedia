-- Prove2me | solution 1 for BookProof.ChapterGaugeCasimirAverage.gaugeAverage_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:25:12.668253+00:00
-- url     : https://prove2.me/submissions/1c81da9a-9d3b-4560-a7b3-1cfad6df54bc

-- Generated from ChapterGaugeCasimirAverage.lean — solution of BookProof.ChapterGaugeCasimirAverage.gaugeAverage_const
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
theorem solution (μ : Measure G) [IsProbabilityMeasure μ] (c : ℝ) :
    gaugeAverage (X := X) μ (fun _ => c) = fun _ => c := by

  funext x
  simp [gaugeAverage]
