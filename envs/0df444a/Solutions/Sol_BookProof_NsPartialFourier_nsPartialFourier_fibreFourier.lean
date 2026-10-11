-- Prove2me | solution 1 for BookProof.NsPartialFourier.nsPartialFourier_fibreFourier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:56:55.928695+00:00
-- url     : https://prove2.me/submissions/cde25078-522a-4025-86df-6ad5eac648e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNsPartialFourier.lean — solution of BookProof.NsPartialFourier.nsPartialFourier_fibreFourier
import Mathlib
import Definitions.Def_ChapterNsPartialFourier
import Theorems.Thm_BookProof_NsPartialFourier_partialFourier_fibreOp
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
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable (W) in

set_option maxHeartbeats 1000000 in
theorem solution
    (f : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) :
    nsPartialFourier V W (fibreOp V (fibreFourierCLM W) f)
      = fibreOp V (fibreFourierCLM W) (nsPartialFourier V W f) := partialFourier_fibreOp _ f
