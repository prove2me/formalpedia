-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.cpoly_harmPoly
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:01:33.242093+00:00
-- url     : https://prove2.me/submissions/fe0146dd-36ba-4262-89f3-520e3a09c75f

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.cpoly_harmPoly
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution : cpoly (harmPoly (d := d)) = harmPoly := by
  have h4 : (starRingEnd ℂ) (4 : ℂ) = 4 := by norm_num [Complex.ext_iff]
  simp [cpoly, harmPoly, h4]

#print axioms solution
