-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.inner_sub_const_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:53.639989+00:00
-- url     : https://prove2.me/submissions/4a8b403b-8d05-4c4b-ab3c-a6ff364c0a35

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.inner_sub_const_smul
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (A : E →L[ℂ] E) (c : ℂ) (x : E) :
    (⟪ x, (A - c • (1 : E →L[ℂ] E)) x ⟫_ℂ) = ⟪ x, A x ⟫_ℂ - c * (‖x‖ ^ 2 : ℝ) := by

  have hx : (A - c • (1 : E →L[ℂ] E)) x = A x - c • x := by
    simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  rw [hx, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
