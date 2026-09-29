-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.norm_sq_one
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:37.768995+00:00
-- url     : https://prove2.me/submissions/f0fb3a59-a66d-4496-a34e-8712fd274400

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.norm_sq_one
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (x : Vd 1) : ‖x‖ ^ 2 = (x 0) ^ 2 := by
  rw [norm_sq_eq_sum x, Fin.sum_univ_one]

#print axioms solution
