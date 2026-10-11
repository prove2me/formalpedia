-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.diagOp_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:35:56.515801+00:00
-- url     : https://prove2.me/submissions/77123fde-03b4-4c81-ab13-163317db5854

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.diagOp_mul
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in


@[simp] private theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem solution (d e : EllInf) : diagOp (d * e) = (diagOp d).comp (diagOp e) := by
  ext f i
  simp [mul_assoc]
