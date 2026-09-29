-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.inner_pgLpT_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T01:22:33.12864+00:00
-- url     : https://prove2.me/submissions/51214e4d-760d-4302-8f66-01d87064ff26

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.inner_pgLpT_left
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.ShiftedHermiteCore











open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) (u : L2d d) :
    (inner ℂ (pgLpT a k p) u : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFunT a k p x) * (u : Vd d → ℂ) x := by

  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [pgLpT_coeFn a k p] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]
