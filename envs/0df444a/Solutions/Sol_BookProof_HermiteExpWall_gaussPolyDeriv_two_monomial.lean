-- Prove2me | solution 1 for BookProof.HermiteExpWall.gaussPolyDeriv_two_monomial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:40.375139+00:00
-- url     : https://prove2.me/submissions/906e0061-06d4-4e23-9334-98b2e7f69917

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.gaussPolyDeriv_two_monomial
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_gaussPolyDeriv_monomial
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
    gaussPolyDeriv (gaussPolyDeriv ((Polynomial.X : Polynomial ℝ) ^ (m + 2)))
      = - kinQ m (aCoef m) (bCoef m) := by
  rw [gaussPolyDeriv_monomial]
  unfold gaussPolyDeriv kinQ oscQ aCoef bCoef
  rw [Polynomial.derivative_sub, Polynomial.derivative_C_mul, Polynomial.derivative_C_mul,
    Polynomial.derivative_X_pow, Polynomial.derivative_X_pow]
  refine Polynomial.funext fun x => ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  push_cast
  ring
