-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.orthonormal_hermiteTLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:17.664294+00:00
-- url     : https://prove2.me/submissions/c8b8b4d9-2d14-4cdd-8b56-e71a380c48aa

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.orthonormal_hermiteTLp
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Theorems.Thm_BookProof_ShiftedHermiteCore_inner_hermiteTLp
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
theorem solution (a k : Vd d) : Orthonormal ℂ (hermiteTLp (d := d) a k) := by

  rw [orthonormal_iff_ite]
  intro α β
  rw [inner_hermiteTLp]
  exact orthonormal_iff_ite.mp orthonormal_hermiteMvLp α β
