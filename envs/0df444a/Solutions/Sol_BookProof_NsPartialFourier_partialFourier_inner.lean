-- Prove2me | solution 1 for BookProof.NsPartialFourier.partialFourier_inner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:56:53.384616+00:00
-- url     : https://prove2.me/submissions/c8ddb82b-0fac-4ee5-b42b-bd3645ad412f

-- Generated from ChapterNsPartialFourier.lean — solution of BookProof.NsPartialFourier.partialFourier_inner
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
theorem solution (v u : Lp F 2 (volume : Measure V)) :
    (inner ℂ (partialFourier V F v) (partialFourier V F u) : ℂ) = inner ℂ v u := (partialFourier V F).inner_map_map v u
