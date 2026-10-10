-- Prove2me | solution 1 for BookProof.ChapterAbelianAtomicCondensation.atomProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:55:10.36629+00:00
-- url     : https://prove2.me/submissions/c76f9093-70a0-43f3-adde-f0808762d1ea

-- Generated from ChapterAbelianAtomicCondensation.lean — solution of BookProof.ChapterAbelianAtomicCondensation.atomProj_apply
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_coordUnit_eq
open BookProof.ChapterAbelianAtomicCondensation



open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

set_option maxHeartbeats 1000000 in
theorem solution (i : ℕ) (f : Ell2C) : atomProj i f = (f : ℕ → ℂ) i • atom i := diagOp_coordUnit_eq i f
