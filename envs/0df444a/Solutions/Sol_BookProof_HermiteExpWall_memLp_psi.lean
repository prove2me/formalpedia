-- Prove2me | solution 1 for BookProof.HermiteExpWall.memLp_psi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:04:43.268105+00:00
-- url     : https://prove2.me/submissions/89e2eedc-bb01-4b33-b789-3f7a1aab0aac

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.memLp_psi
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_psi_sq
import Theorems.Thm_BookProof_QgHermiteCore_continuous_gaussPoly
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterQgHermiteCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.GhostField
open BookProof.HermiteCore
open BookProof.QgHermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) : MemLp (psi N) 2 volume := by

  refine (memLp_two_iff_integrable_sq_norm
    ((continuous_gaussPoly _).aestronglyMeasurable)).mpr ?_
  have h := integrable_poly_mul_gaussW ((Polynomial.X : Polynomial ℝ) ^ (2 * N))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  rw [show gaussPoly ((Polynomial.X : Polynomial ℝ) ^ N) x = psi N x from rfl, psi_sq]
  simp
