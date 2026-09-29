-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.continuous_sectorQuadW
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:29.563035+00:00
-- url     : https://prove2.me/submissions/56c03bc0-af71-4979-a7e1-57abfa273d31

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.continuous_sectorQuadW
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (M alpha mu : ℝ) : Continuous (sectorQuadW M alpha mu) := by
  unfold sectorQuadW confV
  fun_prop

#print axioms solution
