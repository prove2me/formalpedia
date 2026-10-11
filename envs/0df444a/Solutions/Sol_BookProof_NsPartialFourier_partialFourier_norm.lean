-- Prove2me | solution 1 for BookProof.NsPartialFourier.partialFourier_norm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:56:52.21837+00:00
-- url     : https://prove2.me/submissions/e0a1b5de-5d35-42fe-ba72-849ef576b83b

-- Generated from ChapterNsPartialFourier.lean — solution of BookProof.NsPartialFourier.partialFourier_norm
import Mathlib
import Definitions.Def_ChapterNsPartialFourier
open BookProof.NsPartialFourier




open MeasureTheory SchwartzMap FourierTransform LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable (V F) in

set_option maxHeartbeats 1000000 in
theorem solution (v : Lp F 2 (volume : Measure V)) :
    ‖partialFourier V F v‖ = ‖v‖ := (partialFourier V F).norm_map v
