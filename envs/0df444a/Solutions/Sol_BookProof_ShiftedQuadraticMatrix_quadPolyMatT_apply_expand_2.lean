-- Prove2me | solution 2 for BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:29:38.672636+00:00
-- url     : https://prove2.me/submissions/c0e7180e-35b3-4c12-b3ff-4bb33408e5c7

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadraticMatrix



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}
theorem h44x_mulX {d : ℕ} (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    BookProof.NavierStokesFlow.DifferentialL2.mulXPoly i p = MvPolynomial.X i * p := rfl
open BookProof.ShiftedHermiteCore BookProof.NavierStokesFlow.DifferentialL2 MvPolynomial in
theorem h44x_term {d : ℕ} (a k : BookProof.HermiteProductCore.Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (p q : Fin d)
    (f : MvPolynomial (Fin d) ℂ) :
    ((A p q : ℝ) : ℂ) • ((momTPoly k p).comp (momTPoly k q) f
        + (1/4 : ℂ) • ((mulXTPoly a p).comp (mulXTPoly a q) f))
      = ((A p q : ℝ) : ℂ) • (momPoly p (momPoly q f) + (1/4 : ℂ) • (X p * (X q * f)))
        + ((A p q * k q : ℝ) : ℂ) • momPoly p f + ((A p q * k p : ℝ) : ℂ) • momPoly q f
        + ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f) + ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
        + ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f := by
  simp only [momTPoly, mulXTPoly, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul]
  simp only [h44x_mulX]
  push_cast
  module

theorem solution (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ)
    (f : MvPolynomial (Fin d) ℂ) :
    quadPolyMatT a k A f
      = quadPolyMat A f
        + ∑ p, ∑ q, ((A p q * k q : ℝ) : ℂ) • momPoly p f
        + ∑ p, ∑ q, ((A p q * k p : ℝ) : ℂ) • momPoly q f
        + ∑ p, ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f)
        + ∑ p, ∑ q, ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
        + ∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f := by
  rw [quadPolyMatT, quadPolyMat]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, h44x_term]
  simp only [LinearMap.comp_apply, h44x_mulX, Finset.sum_add_distrib]

