-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.vonNeumann_abelian_class_countable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:36:11.159191+00:00
-- url     : https://prove2.me/submissions/58dacff9-60f2-435a-8d7a-53c9bfb85a93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.vonNeumann_abelian_class_countable
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
import Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_injective
import Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_comm
import Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_commutes_diagOp_iff
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    Function.Injective diagOp ∧
      (∀ d e : EllInf, (diagOp d).comp (diagOp e) = (diagOp e).comp (diagOp d)) ∧
      (∀ T : Ell2C →L[ℂ] Ell2C,
        (∀ d : EllInf, T.comp (diagOp d) = (diagOp d).comp T) ↔ ∃ d : EllInf, T = diagOp d) := ⟨diagOp_injective, diagOp_comm, commutes_diagOp_iff⟩
