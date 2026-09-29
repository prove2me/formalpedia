-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.hamCore_congr
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:18:15.414978+00:00
-- url     : https://prove2.me/submissions/ee4f52e2-e1ca-4397-bb85-307db0931994

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.hamCore_congr
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution {U U' : Vd d → ℝ} (h : U = U') (hUc : Continuous U) (hUb : ExpBounded U)
    (hU'c : Continuous U') (hU'b : ExpBounded U') :
    hamCore U hUc hUb = hamCore U' hU'c hU'b := by
  subst h; rfl

#print axioms solution
