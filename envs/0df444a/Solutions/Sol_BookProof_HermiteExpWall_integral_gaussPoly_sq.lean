-- Prove2me | solution 1 for BookProof.HermiteExpWall.integral_gaussPoly_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:35.663786+00:00
-- url     : https://prove2.me/submissions/47e062a1-abc7-4b64-8365-3c877a804787

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.integral_gaussPoly_sq
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_QgHermiteCore_integral_gaussPoly_mul
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

theorem solution (q : Polynomial ℝ) :
    ∫ x : ℝ, gaussPoly q x ^ 2 = gint (q * q) := by
  rw [← integral_gaussPoly_mul q q]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => sq (gaussPoly q x))
