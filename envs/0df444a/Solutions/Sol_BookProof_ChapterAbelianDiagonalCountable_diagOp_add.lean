-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.diagOp_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:35:54.608983+00:00
-- url     : https://prove2.me/submissions/73f6fef0-0c79-4a60-bfbc-0ad772e7bc34

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.diagOp_add
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in


@[simp] private theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem solution (d e : EllInf) : diagOp (d + e) = diagOp d + diagOp e := by
  ext f i
  simp [add_mul]
