-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_symmetric_of_equilibrium
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:33:38.982922+00:00
-- url     : https://prove2.me/submissions/7d7738ce-203c-4c36-8dba-98719f9c9821
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_symmetric_of_equilibrium
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Theorems.Thm_BookProof_QuadraticRotation_exists_rotConj_eigenvalues
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_entries_symm
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_rotConj_symmetric
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
    SymmetricOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b') := by
  obtain ⟨O, hO, hAO⟩ := exists_rotConj_eigenvalues hA
  have hsym := entries_symm hA
  rw [hAO] at hsym ha hk ⊢
  exact shiftedHMatOp_rotConj_symmetric hO _ a k b b' hsym ha hk
