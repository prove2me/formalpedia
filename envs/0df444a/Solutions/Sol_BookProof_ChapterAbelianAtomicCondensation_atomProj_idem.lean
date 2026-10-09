-- Prove2me | solution 1 for BookProof.ChapterAbelianAtomicCondensation.atomProj_idem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:35:54.91011+00:00
-- url     : https://prove2.me/submissions/d91e4a01-c430-43f0-b570-dcf158548c2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAbelianAtomicCondensation.lean — solution of BookProof.ChapterAbelianAtomicCondensation.atomProj_idem
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_mul
open BookProof.ChapterAbelianAtomicCondensation



open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

set_option maxHeartbeats 1000000 in
theorem solution (i : ℕ) : (atomProj i).comp (atomProj i) = atomProj i := by

  rw [atomProj, ← diagOp_mul]
  congr 1
  apply lp.ext
  funext j
  by_cases h : j = i
  · subst h; simp [coordUnit, lp.single_apply]
  · simp [coordUnit, lp.single_apply, h]
