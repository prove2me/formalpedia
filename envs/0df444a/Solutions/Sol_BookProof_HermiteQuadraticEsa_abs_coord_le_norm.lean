-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.abs_coord_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:23.168358+00:00
-- url     : https://prove2.me/submissions/059e49f7-434f-4452-a4a2-53d3f63ecbbb

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.abs_coord_le_norm
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (x : Vd 1) : |x 0| ≤ ‖x‖ := by
  have h : ‖x‖ ^ 2 = (x 0) ^ 2 := by rw [norm_sq_eq_sum x, Fin.sum_univ_one]
  nlinarith [abs_nonneg (x 0), norm_nonneg x, sq_abs (x 0)]

#print axioms solution
