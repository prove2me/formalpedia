-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:57:16.954343+00:00
-- url     : https://prove2.me/submissions/70e7e468-1659-42d8-9cee-dc776b6c6d0a

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_norm_exp_le
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} (h : NumReLE A 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A)‖ ≤ 1 := by

  have := norm_exp_le h ht
  simpa using this
