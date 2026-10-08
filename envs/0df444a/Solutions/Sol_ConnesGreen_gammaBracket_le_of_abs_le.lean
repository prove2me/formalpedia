-- Prove2me | solution 1 for ConnesGreen.gammaBracket_le_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T01:34:35.801994+00:00
-- url     : https://prove2.me/submissions/e43f5ae9-351b-437e-a668-23aafc97f260

import Mathlib
import Theorems.Thm_Zeta23_MuFields_re_digamma_mono
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex
theorem digamma_conj (z : ℂ) :
    Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Complex.digamma z) := by
  have hG : (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) = Complex.Gamma := by
    funext w
    simp only [Function.comp_apply]
    rw [Complex.Gamma_conj]
    exact Complex.conj_conj _
  have hd : deriv Complex.Gamma ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (deriv Complex.Gamma z) := by
    conv_lhs => rw [← hG, deriv_conj_conj]
    simp only [Function.comp_apply, Complex.conj_conj]
  simp only [Complex.digamma_def, logDeriv_apply]
  rw [hd, Complex.Gamma_conj, ← map_div₀]

theorem solution (B r : ℝ) (hB : 0 ≤ B) (hBr : B ≤ |r|) :
    (Complex.digamma (1 / 4 + I * B / 2)).re - Real.log Real.pi ≤
      (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi := by 
  have hm := Zeta23.MuFields.re_digamma_mono (a := 1 / 4) (by norm_num) (by norm_num)
    (show 0 ≤ B / 2 by positivity) (show 0 ≤ |r| / 2 by positivity)
    (div_le_div_of_nonneg_right hBr (by norm_num : (0 : ℝ) ≤ 2))
  have he : ∀ x : ℝ, ((1 / 4 : ℝ) : ℂ) + I * ((x / 2 : ℝ) : ℂ) =
      1 / 4 + I * x / 2 := by intro x; push_cast; ring
  simp only [he] at hm
  have ha : (Complex.digamma (1 / 4 + I * ((|r| : ℝ) : ℂ) / 2)).re =
      (Complex.digamma (1 / 4 + I * r / 2)).re := by
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr]
      have harg : (1 / 4 + I * ((-r : ℝ) : ℂ) / 2 : ℂ) =
          (starRingEnd ℂ) (1 / 4 + I * r / 2) := by
        apply Complex.ext <;> simp [map_ofNat]
      rw [harg, digamma_conj]
      simp
  rw [ha] at hm
  exact sub_le_sub_right hm _
