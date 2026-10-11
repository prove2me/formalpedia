-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_not_bounded
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:45:03.273014+00:00
-- url     : https://prove2.me/submissions/ad42a526-4595-450c-b9a4-175b9ccaddba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_not_bounded
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_mulVec_matShiftVec
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_mulVec_matBoostVec
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_entries_symm
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_rotConj_not_bounded
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
    (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) (i : Fin d) :
    ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT (matShiftVec A b) (matBoostVec A b'),
        ‖shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b' f‖
          ≤ C * ‖(f : L2d d)‖ := by

  obtain ⟨O, hO, hAO⟩ := exists_rotConj_eigenvalues hA
  have hsym := entries_symm hA
  have heig : hA.eigenvalues i ≠ 0 := by
    have hprod : (∏ j, hA.eigenvalues j) ≠ 0 := by
      have := hA.det_eq_prod_eigenvalues
      simp only [RCLike.ofReal_real_eq_id, id_eq] at this
      rw [← this]
      exact isUnit_iff_ne_zero.mp hdet
    exact fun h0 => hprod (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  rw [hAO] at hsym hdet ⊢
  exact shiftedHMatOp_rotConj_not_bounded hO _ _ _ b b' hsym
    (mulVec_matShiftVec hdet b) (mulVec_matBoostVec hdet b') heig
