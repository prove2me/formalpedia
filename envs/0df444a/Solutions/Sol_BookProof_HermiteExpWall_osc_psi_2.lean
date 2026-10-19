-- Prove2me | solution 2 for BookProof.HermiteExpWall.osc_psi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:47:43.206279+00:00
-- url     : https://prove2.me/submissions/b67f9951-1c73-46ea-9b73-dbd21578261b

import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_deriv2_gaussPoly
import Theorems.Thm_BookProof_HermiteExpWall_gaussPolyDeriv_two_monomial
-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.osc_psi
open BookProof.GhostField
open BookProof.HermiteCore
open BookProof.QgHermiteCore
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section


theorem solution (m : ℕ) :
    (fun x => -deriv (deriv (BookProof.HermiteExpWall.psi (m + 2))) x + x ^ 2 / 4 * BookProof.HermiteExpWall.psi (m + 2) x)
      = gaussPoly (oscQ m (aCoef m) (bCoef m)) := by
  funext x
  unfold BookProof.HermiteExpWall.psi
  rw [BookProof.QgHermiteCore.deriv2_gaussPoly, BookProof.HermiteExpWall.gaussPolyDeriv_two_monomial]
  simp only [BookProof.QgHermiteCore.gaussPoly, BookProof.HermiteExpWall.kinQ,
    BookProof.HermiteExpWall.oscQ, Polynomial.eval_neg, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

