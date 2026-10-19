-- Prove2me | solution 1 for BookProof.NsPartialFourier.nsPartialFourier_fibreOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:56:54.656292+00:00
-- url     : https://prove2.me/submissions/f5cc70d5-9e5e-4897-a119-ebde3ea1d54a

-- Generated from ChapterNsPartialFourier.lean — solution of BookProof.NsPartialFourier.nsPartialFourier_fibreOp
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
variable (V W) in

set_option maxHeartbeats 1000000 in
theorem solution (T : Lp ℂ 2 (volume : Measure W) →L[ℂ] Lp ℂ 2 (volume : Measure W))
    (f : Lp (Lp ℂ 2 (volume : Measure W)) 2 (volume : Measure V)) :
    nsPartialFourier V W (fibreOp V T f) = fibreOp V T (nsPartialFourier V W f) := partialFourier_fibreOp T f
