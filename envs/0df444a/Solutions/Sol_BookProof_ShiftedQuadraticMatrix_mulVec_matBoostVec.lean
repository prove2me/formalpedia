-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.mulVec_matBoostVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:43:52.126697+00:00
-- url     : https://prove2.me/submissions/06cba09e-8bea-41ed-b1fd-93007e47673d

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.mulVec_matBoostVec
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
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
theorem solution {A : Matrix (Fin d) (Fin d) ℝ} (hdet : IsUnit A.det)
    (b' : Fin d → ℝ) (i : Fin d) :
    ∑ j, A i j * (matBoostVec A b') j = -(b' i) / 2 := by

  have h : A *ᵥ (A⁻¹ *ᵥ fun j => -(b' j) / 2) = fun j => -(b' j) / 2 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  calc ∑ j, A i j * (matBoostVec A b') j
      = (A *ᵥ (A⁻¹ *ᵥ fun j => -(b' j) / 2)) i := rfl
    _ = -(b' i) / 2 := by rw [h]
