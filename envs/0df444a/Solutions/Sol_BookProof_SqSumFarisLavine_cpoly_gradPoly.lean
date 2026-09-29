-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.cpoly_gradPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T09:56:27.633559+00:00
-- url     : https://prove2.me/submissions/f3dde765-0231-42ec-b846-840022913d7e

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.cpoly_gradPoly
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_cpoly_linForm
import Theorems.Thm_BookProof_GaussCoreQuadBounds_cpoly_real_smul
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterFarisLavine
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_sum
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (v : R → Fin D → ℝ) (k : Fin D) :
    cpoly (gradPoly v k) = gradPoly v k := by

  rw [gradPoly, cpoly_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [cpoly_real_smul, cpoly_linForm]
