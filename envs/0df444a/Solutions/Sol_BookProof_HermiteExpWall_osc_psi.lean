-- Prove2me | solution 1 for BookProof.HermiteExpWall.osc_psi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:20.082733+00:00
-- url     : https://prove2.me/submissions/a364227f-40d9-4a33-a8f4-d19bcac78b37

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.osc_psi
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_psi_apply
import Theorems.Thm_BookProof_HermiteExpWall_neg_deriv2_psi
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

theorem solution (m : ℕ) :
    (fun x => -deriv (deriv (psi (m + 2))) x + x ^ 2 / 4 * psi (m + 2) x)
      = gaussPoly (oscQ m (aCoef m) (bCoef m)) := by
  funext x
  have h := congrFun (neg_deriv2_psi m) x
  rw [h, psi_apply]
  simp only [kinQ, gaussPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring
