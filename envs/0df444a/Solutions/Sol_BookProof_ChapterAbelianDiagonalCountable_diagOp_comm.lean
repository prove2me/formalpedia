-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.diagOp_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:35:58.564831+00:00
-- url     : https://prove2.me/submissions/ad9a1704-fa5f-4540-9781-ac0ce58a5e4a

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.diagOp_comm
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in

@[simp] private theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem solution (d e : EllInf) :
    (diagOp d).comp (diagOp e) = (diagOp e).comp (diagOp d) := by
  ext f i
  simp [mul_left_comm]
