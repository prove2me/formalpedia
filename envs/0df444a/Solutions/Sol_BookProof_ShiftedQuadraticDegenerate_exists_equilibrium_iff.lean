-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.exists_equilibrium_iff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:33:10.336313+00:00
-- url     : https://prove2.me/submissions/226ff6e1-8317-4d16-b781-501b4577d4de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.exists_equilibrium_iff
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_equilibrium_orthogonal_to_kernel
import Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_exists_equilibrium
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_entries_symm
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
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

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (w : Fin d → ℝ) :
    (∃ a : Fin d → ℝ, ∀ i, ∑ j, A i j * a j = w i)
      ↔ ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, w i * v i = 0 := by

  refine ⟨fun ⟨a, ha⟩ v hv => equilibrium_orthogonal_to_kernel (entries_symm hA) ha hv,
    fun hw => exists_equilibrium hA hw⟩
