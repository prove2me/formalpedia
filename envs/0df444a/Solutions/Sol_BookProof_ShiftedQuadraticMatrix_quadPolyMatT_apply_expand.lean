-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:43:00.506451+00:00
-- url     : https://prove2.me/submissions/0d32bdab-0c77-4e6c-ac8c-eef981c2c453

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_quadTermT_apply
import Theorems.Thm_BookProof_QuadraticRotation_quadPolyMat_apply
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
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

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ)
    (f : MvPolynomial (Fin d) ℂ) :
    quadPolyMatT a k A f
      = quadPolyMat A f
        + ∑ p, ∑ q, ((A p q * k q : ℝ) : ℂ) • momPoly p f
        + ∑ p, ∑ q, ((A p q * k p : ℝ) : ℂ) • momPoly q f
        + ∑ p, ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f)
        + ∑ p, ∑ q, ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
        + ∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f := by

  rw [quadPolyMatT]
  simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    quadTermT_apply a k A p q f]
  simp only [Finset.sum_add_distrib]
  rw [quadPolyMat_apply]
