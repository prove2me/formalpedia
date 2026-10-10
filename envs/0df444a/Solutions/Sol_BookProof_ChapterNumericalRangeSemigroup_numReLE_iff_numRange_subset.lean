-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:57.845839+00:00
-- url     : https://prove2.me/submissions/f38a9796-cc5c-4d82-bdba-d5a183e65f60

-- Generated from ChapterNumericalRangeSemigroup.lean — solution of BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Theorems.Thm_BookProof_ChapterH9_mem_numRange
import Definitions.Def_ChapterH9
open BookProof.ChapterNumericalRangeSemigroup



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (A : E →L[ℂ] E) {ω : ℝ} :
    NumReLE A ω ↔ BookProof.ChapterH9.numRange A ⊆ {z : ℂ | z.re ≤ ω} := by

  constructor
  · rintro h z ⟨x, hx, rfl⟩
    have := h x
    rw [hx] at this
    simpa using this
  · intro h x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      set y : E := (‖x‖ : ℂ)⁻¹ • x with hy
      have hynorm : ‖y‖ = 1 := by
        rw [hy, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          inv_mul_cancel₀ hxnorm]
      have hmem : (inner ℂ y (A y) : ℂ) ∈ BookProof.ChapterH9.numRange A :=
        BookProof.ChapterH9.mem_numRange y hynorm
      have hbound : (inner ℂ y (A y) : ℂ).re ≤ ω := h hmem
      have hexp : (inner ℂ y (A y) : ℂ) = ((‖x‖ : ℂ)⁻¹ * (‖x‖ : ℂ)⁻¹) * inner ℂ x (A x) := by
        rw [hy]
        rw [inner_smul_left, map_smul, inner_smul_right]
        simp [Complex.conj_ofReal]
        ring
      have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
      have hre : (inner ℂ y (A y) : ℂ).re = (inner ℂ x (A x) : ℂ).re / ‖x‖ ^ 2 := by
        rw [hexp]
        have : ((‖x‖ : ℂ)⁻¹ * (‖x‖ : ℂ)⁻¹) = (((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
          push_cast
          rw [sq]
          field_simp
        rw [this, Complex.re_ofReal_mul]
        field_simp
      rw [hre] at hbound
      rw [div_le_iff₀ (by positivity)] at hbound
      linarith [hbound]
