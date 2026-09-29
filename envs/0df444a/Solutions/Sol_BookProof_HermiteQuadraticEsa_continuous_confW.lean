-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.continuous_confW
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:28.683035+00:00
-- url     : https://prove2.me/submissions/2c0e7bed-2e85-43cf-b4ea-46e0f10c50da

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.continuous_confW
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (M alpha : ℝ) : Continuous (confW M alpha) := by
  unfold confW confV
  fun_prop

#print axioms solution
