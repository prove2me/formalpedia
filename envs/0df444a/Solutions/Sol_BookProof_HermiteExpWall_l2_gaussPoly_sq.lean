-- Prove2me | solution 1 for BookProof.HermiteExpWall.l2_gaussPoly_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:36.797005+00:00
-- url     : https://prove2.me/submissions/68b09349-5e1d-4e4d-b950-7c2faf3ea613

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.l2_gaussPoly_sq
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_integral_gaussPoly_sq
import Theorems.Thm_BookProof_HermiteExpWall_gint_self_nonneg
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterQgHermiteCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.HermiteCore
open BookProof.QgHermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in

theorem solution (q : Polynomial ℝ) : l2 (gaussPoly q) ^ 2 = gint (q * q) := by
  rw [l2, Real.sq_sqrt (by rw [integral_gaussPoly_sq]; exact gint_self_nonneg q)]
  exact integral_gaussPoly_sq q
