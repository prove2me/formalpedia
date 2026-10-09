-- Prove2me | solution 1 for BookProof.GraphCore.deficiencyTrivialAt_of_bounded_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:49:17.016659+00:00
-- url     : https://prove2.me/submissions/74c8fd82-6aaf-4c09-8c15-205766fe378d

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.deficiencyTrivialAt_of_bounded_dense
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Theorems.Thm_BookProof_FarisLavine_inner_apply_self_im
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (hT : SymmetricOn D T) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : D, ‖T x‖ ≤ C * ‖(x : F)‖)
    (hdense : Dense (D : Set F)) {d : ℝ} (hd : d ≠ 0) :
    DeficiencyTrivialAt D T ((d : ℂ) * Complex.I) := by

  intro w hw
  have key : ∀ ε > 0, |d| * ‖w‖ ^ 2 ≤ (C * (‖w‖ + 1) + |d| * ‖w‖) * ε := by
    intro ε hε
    set e : ℝ := min ε 1 with he
    have hepos : 0 < e := lt_min hε one_pos
    have hele : e ≤ ε := min_le_left _ _
    obtain ⟨v, hvD, hv⟩ := Metric.mem_closure_iff.mp (hdense w) e hepos
    have hvw : ‖w - v‖ < e := by rw [← dist_eq_norm]; exact hv
    have hvnorm : ‖v‖ ≤ ‖w‖ + 1 := by
      have h1 : ‖v‖ - ‖w‖ ≤ ‖v - w‖ := by simpa using norm_sub_norm_le v w
      have h2 : ‖v - w‖ = ‖w - v‖ := norm_sub_rev v w
      have h3 : e ≤ 1 := min_le_right _ _
      linarith
    have heq := hw ⟨v, hvD⟩
    have hsplit : (inner ℂ (T ⟨v, hvD⟩) w : ℂ)
        = inner ℂ (T ⟨v, hvD⟩) (v : F) + inner ℂ (T ⟨v, hvD⟩) (w - v) := by
      rw [← inner_add_right]; congr 1; abel
    have hreal : (inner ℂ (T ⟨v, hvD⟩) (v : F) : ℂ).im = 0 :=
      inner_apply_self_im T hT ⟨v, hvD⟩
    have hsmall : ‖(inner ℂ (T ⟨v, hvD⟩) (w - v) : ℂ)‖ ≤ C * (‖w‖ + 1) * e := by
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      have h1 : ‖T ⟨v, hvD⟩‖ ≤ C * (‖w‖ + 1) :=
        le_trans (hC ⟨v, hvD⟩) (mul_le_mul_of_nonneg_left hvnorm hC0)
      exact mul_le_mul h1 hvw.le (norm_nonneg _) (by positivity)
    have hrhs : ((d : ℂ) * Complex.I * inner ℂ (v : F) w : ℂ)
        = (d : ℂ) * Complex.I * (inner ℂ w w) - (d : ℂ) * Complex.I * inner ℂ (w - v) w := by
      rw [← mul_sub, ← inner_sub_left]; congr 2; abel
    have hww : (inner ℂ w w : ℂ) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    have himL : (inner ℂ (T ⟨v, hvD⟩) w : ℂ).im
        = (inner ℂ (T ⟨v, hvD⟩) (w - v) : ℂ).im := by
      rw [hsplit]; simp [hreal]
    have himR : ((d : ℂ) * Complex.I * inner ℂ (v : F) w : ℂ).im
        = d * ‖w‖ ^ 2 - ((d : ℂ) * Complex.I * inner ℂ (w - v) w : ℂ).im := by
      rw [hrhs, hww]
      simp only [Complex.ofReal_pow, CStarModule.inner_sub_left, inner_self_eq_norm_sq_to_K,
        Complex.coe_algebraMap, Complex.sub_im, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, zero_mul, add_zero, zero_add, Complex.sub_re, sub_left_inj,
        mul_eq_mul_left_iff]
      left
      simp [pow_two, Complex.mul_re]
    have hbound2 : ‖((d : ℂ) * Complex.I * inner ℂ (w - v) w : ℂ)‖ ≤ |d| * ‖w‖ * e := by
      rw [norm_mul, norm_mul]
      have h1 : ‖(inner ℂ (w - v) w : ℂ)‖ ≤ e * ‖w‖ :=
        le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
          (mul_le_mul_of_nonneg_right hvw.le (norm_nonneg w))
      have hd' : ‖((d : ℂ))‖ = |d| := by simp
      rw [hd']
      simp only [Complex.norm_I, mul_one]
      calc |d| * ‖(inner ℂ (w - v) w : ℂ)‖ ≤ |d| * (e * ‖w‖) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg d)
        _ = |d| * ‖w‖ * e := by ring
    have hfinal : d * ‖w‖ ^ 2
        = (inner ℂ (T ⟨v, hvD⟩) (w - v) : ℂ).im
          + ((d : ℂ) * Complex.I * inner ℂ (w - v) w : ℂ).im := by
      have h := congrArg Complex.im heq
      rw [himL, himR] at h
      linarith
    have h1 : |(inner ℂ (T ⟨v, hvD⟩) (w - v) : ℂ).im| ≤ C * (‖w‖ + 1) * e :=
      le_trans (Complex.abs_im_le_norm _) hsmall
    have h2 : |((d : ℂ) * Complex.I * inner ℂ (w - v) w : ℂ).im| ≤ |d| * ‖w‖ * e :=
      le_trans (Complex.abs_im_le_norm _) hbound2
    have h3 : |d * ‖w‖ ^ 2| ≤ C * (‖w‖ + 1) * e + |d| * ‖w‖ * e := by
      rw [hfinal]
      exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    have h4 : |d| * ‖w‖ ^ 2 ≤ C * (‖w‖ + 1) * e + |d| * ‖w‖ * e := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖w‖ ^ 2)] at h3
      exact h3
    have hexp : C * (‖w‖ + 1) * e + |d| * ‖w‖ * e
        = (C * (‖w‖ + 1) + |d| * ‖w‖) * e := by ring
    have hmono : (C * (‖w‖ + 1) + |d| * ‖w‖) * e ≤ (C * (‖w‖ + 1) + |d| * ‖w‖) * ε := by
      have hnn : 0 ≤ C * (‖w‖ + 1) + |d| * ‖w‖ := by positivity
      exact mul_le_mul_of_nonneg_left hele hnn
    linarith
  have hzero : ‖w‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hne)
    have hd0 : 0 < |d| := abs_pos.mpr hd
    set K : ℝ := C * (‖w‖ + 1) + |d| * ‖w‖ with hK
    have hKpos : 0 < K := by
      have hA : 0 ≤ C * (‖w‖ + 1) := by positivity
      have hB : 0 < |d| * ‖w‖ := mul_pos hd0 hpos
      simp only [hK]; linarith
    have hgoal : 0 < |d| * ‖w‖ ^ 2 := by positivity
    have hK0 : K ≠ 0 := ne_of_gt hKpos
    have hcalc : ((|d| * ‖w‖ ^ 2) / (2 * K)) * K = (|d| * ‖w‖ ^ 2) / 2 := by field_simp
    have hkey := key ((|d| * ‖w‖ ^ 2) / (2 * K)) (by positivity)
    rw [mul_comm K] at hkey
    linarith
  exact norm_eq_zero.mp hzero
