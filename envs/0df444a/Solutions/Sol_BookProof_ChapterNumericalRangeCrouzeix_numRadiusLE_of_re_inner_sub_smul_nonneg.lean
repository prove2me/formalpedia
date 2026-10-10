-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_of_re_inner_sub_smul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:37.490434+00:00
-- url     : https://prove2.me/submissions/0ce8ea14-9f4c-45c2-a2e9-9307c97c80fc

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_of_re_inner_sub_smul_nonneg
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_inner_self_re
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {A : E →L[ℂ] E}
    (h : ∀ z : ℂ, ‖z‖ < 1 → ∀ x : E, 0 ≤ (⟪x, x - z • A x⟫_ℂ).re) : NumRadiusLE A 1 := by

  intro x
  by_cases hc : ⟪x, A x⟫_ℂ = 0
  · rw [hc]; simp
  · set c := ⟪x, A x⟫_ℂ with hcdef
    have hcn : (0:ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    have hcn' : (‖c‖ : ℂ) ≠ 0 := by simpa using hc
    have key : ∀ t : ℝ, 0 ≤ t → t < 1 → t * ‖c‖ ≤ ‖x‖ ^ 2 := by
      intro t ht ht1
      have hz : ‖((t : ℂ) * (starRingEnd ℂ) c / (‖c‖ : ℂ))‖ < 1 := by
        rw [norm_div, norm_mul]
        simp only [Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
        rw [abs_of_nonneg ht, abs_of_nonneg (norm_nonneg c), mul_div_assoc,
          div_self hcn.ne']
        simpa using ht1
      have hpos := h _ hz x
      rw [inner_sub_right, inner_smul_right] at hpos
      have hmul : ((t : ℂ) * (starRingEnd ℂ) c / (‖c‖ : ℂ)) * c = ((t * ‖c‖ : ℝ) : ℂ) := by
        have h1 : (starRingEnd ℂ) c * c = ((‖c‖ : ℂ)) ^ 2 := by rw [Complex.conj_mul']
        calc (t:ℂ) * (starRingEnd ℂ) c / (‖c‖:ℂ) * c
            = (t:ℂ) * ((starRingEnd ℂ) c * c) / (‖c‖:ℂ) := by ring
          _ = (t:ℂ) * (‖c‖:ℂ)^2 / (‖c‖:ℂ) := by rw [h1]
          _ = (t:ℂ) * (‖c‖:ℂ) := by field_simp
          _ = ((t * ‖c‖ : ℝ) : ℂ) := by push_cast; ring
      rw [← hcdef, hmul] at hpos
      simp only [Complex.sub_re, Complex.ofReal_re, inner_self_re] at hpos
      linarith
    by_contra hcon
    push_neg at hcon
    rw [one_mul] at hcon
    set t := (‖x‖ ^ 2 / ‖c‖ + 1) / 2 with htdef
    have hx2 : ‖x‖ ^ 2 / ‖c‖ < 1 := (div_lt_one hcn).mpr hcon
    have hx0 : 0 ≤ ‖x‖ ^ 2 / ‖c‖ := by positivity
    have ht0 : 0 ≤ t := by rw [htdef]; linarith
    have ht1 : t < 1 := by rw [htdef]; linarith
    have hkey := key t ht0 ht1
    have hgt : ‖x‖ ^ 2 / ‖c‖ < t := by rw [htdef]; linarith
    rw [div_lt_iff₀ hcn] at hgt
    linarith
