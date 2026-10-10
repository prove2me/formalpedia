-- Prove2me | solution 1 for BookProof.HermiteExpWall.gaussPolyDeriv_monomial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T06:21:08.697694+00:00
-- url     : https://prove2.me/submissions/db946f6e-c99d-4b2f-a967-efe68675c7da

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.gaussPolyDeriv_monomial
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) :
    gaussPolyDeriv ((Polynomial.X : Polynomial ℝ) ^ (m + 2))
      = Polynomial.C ((m : ℝ) + 2) * Polynomial.X ^ (m + 1)
        - Polynomial.C (1 / 2 : ℝ) * Polynomial.X ^ (m + 3) := by
    unfold gaussPolyDeriv
    rw [Polynomial.derivative_X_pow]
    push_cast
    ring

