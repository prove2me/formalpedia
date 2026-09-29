-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.norm_sq_two
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:38.678587+00:00
-- url     : https://prove2.me/submissions/19a98198-5420-4261-b88c-4fd01f340cc3

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.norm_sq_two
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (x : Vd 2) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [norm_sq_eq_sum x, Fin.sum_univ_two]

#print axioms solution
