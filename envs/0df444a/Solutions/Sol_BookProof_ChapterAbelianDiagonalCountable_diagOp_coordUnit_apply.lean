-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T17:59:24.679821+00:00
-- url     : https://prove2.me/submissions/1ec11be4-1a87-4737-9637-d755f3c9b398

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_apply
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section


@[simp] private theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

set_option maxHeartbeats 1000000 in
theorem solution (i : ℕ) (f : Ell2C) (j : ℕ) :
    ((diagOp (coordUnit i) f : Ell2C) : ℕ → ℂ) j = if j = i then (f : ℕ → ℂ) i else 0 := by

  rw [diagOp_apply]
  by_cases h : j = i
  · subst h; simp [coordUnit, lp.single_apply]
  · simp [coordUnit, lp.single_apply, h]
