-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.norm_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:57:15.873326+00:00
-- url     : https://prove2.me/submissions/424c5365-94ff-4ed7-9717-3bfe29ec68ee

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.norm_exp_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_norm_exp_apply_le
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A)‖ ≤ Real.exp (ω * t) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
      (fun x => norm_exp_apply_le h x ht)
