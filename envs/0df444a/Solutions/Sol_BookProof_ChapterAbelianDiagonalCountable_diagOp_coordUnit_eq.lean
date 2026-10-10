-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:35:59.184994+00:00
-- url     : https://prove2.me/submissions/023f4129-cb6e-4d18-ab76-d2ec5ff607d5

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_eq
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
import Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_coordUnit_apply
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (i : ℕ) (f : Ell2C) :
    diagOp (coordUnit i) f = (f : ℕ → ℂ) i • atom i := by

  apply lp.ext
  funext j
  rw [diagOp_coordUnit_apply]
  by_cases h : j = i
  · subst h; simp [atom, lp.single_apply]
  · simp [atom, lp.single_apply, h]
