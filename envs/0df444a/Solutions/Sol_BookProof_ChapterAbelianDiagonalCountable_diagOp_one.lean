-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.diagOp_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:35:57.57282+00:00
-- url     : https://prove2.me/submissions/9df7a090-ab48-4725-b790-d96248ba413c

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.diagOp_one
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in


@[simp] private theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem solution : diagOp (1 : EllInf) = ContinuousLinearMap.id ℂ Ell2C := by
  ext f i
  simp
