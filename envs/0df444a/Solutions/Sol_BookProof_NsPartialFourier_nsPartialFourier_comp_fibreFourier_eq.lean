-- Prove2me | solution 1 for BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:19:58.859559+00:00
-- url     : https://prove2.me/submissions/3fdafbda-f112-434e-bee0-674a45d907cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNsPartialFourier.lean — solution of BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq
import Mathlib
import Definitions.Def_ChapterNsPartialFourier
import Theorems.Thm_BookProof_NsPartialFourier_nsPartialFourier_fibreFourier
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
theorem solution :
    ((nsPartialFourier V W).toLinearIsometry.toContinuousLinearMap).comp
        (fibreOp V (fibreFourierCLM W))
      = (fibreOp V (fibreFourierCLM W)).comp
        ((nsPartialFourier V W).toLinearIsometry.toContinuousLinearMap) := ContinuousLinearMap.ext fun f => nsPartialFourier_fibreFourier f
