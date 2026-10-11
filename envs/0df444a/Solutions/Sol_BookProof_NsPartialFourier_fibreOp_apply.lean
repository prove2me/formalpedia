-- Prove2me | solution 1 for BookProof.NsPartialFourier.fibreOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:39.90382+00:00
-- url     : https://prove2.me/submissions/cbdb46a1-fa2f-4ba1-b66f-cb29309d59f7

-- Generated from ChapterNsPartialFourier.lean — solution of BookProof.NsPartialFourier.fibreOp_apply
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
variable (V) in

set_option maxHeartbeats 1000000 in
omit [CompleteSpace F] [CompleteSpace G] in
theorem solution (T : F →L[ℂ] G) (f : Lp F 2 (volume : Measure V)) :
    fibreOp V T f = T.compLp f := rfl
