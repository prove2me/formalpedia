-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.norm_le_two_mul_of_numRadiusLE
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:46.486284+00:00
-- url     : https://prove2.me/submissions/8861fd05-a788-44d1-be1a-930546c24760

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.norm_le_two_mul_of_numRadiusLE
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_inner_polar_bound
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r)
    (h : NumRadiusLE A r) : ‖A‖ ≤ 2 * r := by

  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun y => ?_
  rcases eq_or_ne (A y) 0 with hAy | hAy
  · rw [hAy]
    simp
    positivity
  · have hAy0 : 0 < ‖A y‖ := norm_pos_iff.mpr hAy
    have hy0 : 0 < ‖y‖ := by
      rcases eq_or_ne y 0 with rfl | hy
      · simp at hAy
      · exact norm_pos_iff.mpr hy
    set t : ℝ := ‖y‖ / ‖A y‖ with ht
    have htv : t * ‖A y‖ = ‖y‖ := by rw [ht, div_mul_cancel₀ _ hAy0.ne']
    have ht0 : 0 ≤ t := by positivity
    have hb := inner_polar_bound h ((t : ℂ) • A y) y
    have hinner : (⟪A y, (t : ℂ) • A y⟫_ℂ) = ((t * ‖A y‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have hnormx : ‖((t : ℂ) • A y)‖ = t * ‖A y‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    have habs : ‖(((t * ‖A y‖ ^ 2 : ℝ)) : ℂ)‖ = t * ‖A y‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hinner, hnormx, habs] at hb
    have hleft : t * ‖A y‖ ^ 2 = ‖y‖ * ‖A y‖ := by
      rw [pow_two, ← mul_assoc, htv]
    rw [hleft, htv] at hb
    nlinarith [hb, hy0]
