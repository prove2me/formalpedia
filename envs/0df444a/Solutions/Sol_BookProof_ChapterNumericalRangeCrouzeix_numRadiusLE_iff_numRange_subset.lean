-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_iff_numRange_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:34.519361+00:00
-- url     : https://prove2.me/submissions/9570be13-6007-4ba9-b58f-05e1112dccf5

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_iff_numRange_subset
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterH9_mem_numRange
import Definitions.Def_ChapterH9
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] (A : E →L[ℂ] E) {r : ℝ} :
    NumRadiusLE A r ↔ BookProof.ChapterH9.numRange A ⊆ Metric.closedBall (0 : ℂ) r := by

  constructor
  · rintro h c ⟨x, hx, rfl⟩
    simpa [hx] using h x
  · intro h x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
      set y : E := (‖x‖ : ℂ)⁻¹ • x with hy
      have hynorm : ‖y‖ = 1 := by
        rw [hy, norm_smul]
        simp [abs_of_pos hx0, hx0.ne']
      have hmem : (⟪y, A y⟫_ℂ) ∈ BookProof.ChapterH9.numRange A :=
        BookProof.ChapterH9.mem_numRange y hynorm
      have hb : ‖(⟪y, A y⟫_ℂ)‖ ≤ r := by simpa using h hmem
      have hval : (⟪y, A y⟫_ℂ) = ((‖x‖ : ℂ) ^ 2)⁻¹ * (⟪x, A x⟫_ℂ) := by
        rw [hy, inner_smul_left, map_smul, inner_smul_right]
        simp [Complex.conj_ofReal]
        ring
      have hxc : ((‖x‖ : ℂ)) ≠ 0 := by simpa using hx0.ne'
      have : ‖(⟪x, A x⟫_ℂ)‖ = ‖x‖ ^ 2 * ‖(⟪y, A y⟫_ℂ)‖ := by
        rw [hval, norm_mul, norm_inv]
        simp [abs_of_pos hx0]
        field_simp
      rw [this]
      have h2 : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
      nlinarith [hb, h2]
