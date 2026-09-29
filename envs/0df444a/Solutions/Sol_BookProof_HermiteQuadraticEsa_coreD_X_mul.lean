-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.coreD_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:30.67847+00:00
-- url     : https://prove2.me/submissions/e73597b7-5c73-4f71-bd3e-4bcaf90655e1

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.coreD_X_mul
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    coreD j (X j * p) = p + X j * coreD j p := by
  unfold coreD
  rw [pderiv_mul, pderiv_X_self]
  ring

#print axioms solution
