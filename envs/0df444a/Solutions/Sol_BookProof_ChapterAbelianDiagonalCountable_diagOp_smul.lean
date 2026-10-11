-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.diagOp_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:35:55.541471+00:00
-- url     : https://prove2.me/submissions/834c7bc2-9ee3-4776-922d-7aba2362c011

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.diagOp_smul
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in


@[simp] private theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem solution (c : ℂ) (d : EllInf) : diagOp (c • d) = c • diagOp d := by
  ext f i
  simp [mul_assoc]
