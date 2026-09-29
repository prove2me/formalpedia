-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.cpoly_linForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:41:09.340986+00:00
-- url     : https://prove2.me/submissions/57898e4a-ac09-4aca-b7de-5058f75990ce

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.cpoly_linForm
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_GaussCoreQuadBounds_cpoly_real_smul
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterFarisLavine
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_sum
import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_X
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin D → ℝ) : cpoly (linForm v) = linForm v := by

  rw [linForm, cpoly_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [cpoly_real_smul, cpoly_X]
