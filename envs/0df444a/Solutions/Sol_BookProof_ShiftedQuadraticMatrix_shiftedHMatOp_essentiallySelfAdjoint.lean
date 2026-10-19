-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:44:20.00559+00:00
-- url     : https://prove2.me/submissions/cef4f3ae-fad1-424f-a0b3-7242746f5d2c

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_rotConj_deficiencyTrivialAt
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_mulVec_matShiftVec
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_mulVec_matBoostVec
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_entries_symm
import Theorems.Thm_BookProof_QuadraticRotation_exists_rotConj_eigenvalues
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
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
theorem solution {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCoreT (matShiftVec A b) (matBoostVec A b'))
      (shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b') := by

  obtain ⟨O, hO, hAO⟩ := exists_rotConj_eigenvalues hA
  have hsym := entries_symm hA
  rw [hAO] at hsym hdet ⊢
  exact ⟨shiftedHMatOp_rotConj_deficiencyTrivialAt hO _ _ _ b b' hsym
      (mulVec_matShiftVec hdet b) (mulVec_matBoostVec hdet b') (by simp),
    shiftedHMatOp_rotConj_deficiencyTrivialAt hO _ _ _ b b' hsym
      (mulVec_matShiftVec hdet b) (mulVec_matBoostVec hdet b') (by simp)⟩
