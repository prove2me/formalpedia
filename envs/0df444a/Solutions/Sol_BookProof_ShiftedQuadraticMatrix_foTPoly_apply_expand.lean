-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.foTPoly_apply_expand
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:30:42.271002+00:00
-- url     : https://prove2.me/submissions/98dcda9b-ee8d-4778-9fe5-a53b2968c587

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
-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.foTPoly_apply_expand
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

theorem solution (a k : Vd d) (b b' : Fin d → ℝ) (f : MvPolynomial (Fin d) ℂ) :
    foTPoly a k b b' f
      = ∑ i, ((b i : ℝ) : ℂ) • (X i * f) + ∑ i, ((b' i : ℝ) : ℂ) • momPoly i f
        + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f := by
  rw [foTPoly]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, momTPoly, mulXTPoly,
    LinearMap.id_apply, h44x_mulX, smul_add, smul_smul]
  push_cast
  simp only [Finset.sum_smul, add_smul, Finset.sum_add_distrib]
  abel

