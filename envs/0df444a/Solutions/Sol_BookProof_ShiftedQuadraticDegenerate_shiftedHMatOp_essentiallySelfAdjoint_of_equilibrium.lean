-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:33:39.945414+00:00
-- url     : https://prove2.me/submissions/8e1adea8-c924-43ec-a470-dd5600cc0fb6

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Theorems.Thm_BookProof_QuadraticRotation_exists_rotConj_eigenvalues
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_entries_symm
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_rotConj_deficiencyTrivialAt
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadraticDegenerate




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.ShiftedQuadraticMatrix
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.StoneEigenflow
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (b b' : Fin d → ℝ) (a k : Vd d)
    (ha : ∀ i, ∑ j, A i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, A i j * k j = -(b' i) / 2) :
    EssentiallySelfAdjointOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b') := by
  obtain ⟨O, hO, hAO⟩ := exists_rotConj_eigenvalues hA
  have hsym := entries_symm hA
  rw [hAO] at hsym ha hk ⊢
  exact ⟨shiftedHMatOp_rotConj_deficiencyTrivialAt hO _ a k b b' hsym ha hk (by simp),
    shiftedHMatOp_rotConj_deficiencyTrivialAt hO _ a k b b' hsym ha hk (by simp)⟩
