-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_collinear_critical_position_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:29:18.817247+00:00
-- url     : https://prove2.me/submissions/e1bef247-c188-4a9e-bdc6-3bb12a5602d1

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_one
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum

open BirkhoffGlobalSection

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hfree : collisionFree μ s)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s)
    (haxis : s 1 = 0) (hleft : -μ < s 0) (hright : s 0 < 1 - μ) :
    s 0 = L 0 := by
  have balance (t : Phase) (hf : collisionFree μ t)
      (hc : isCriticalPoint (jacobiHamiltonian μ) t)
      (ha : t 1 = 0) (hl : -μ < t 0) (hu : t 0 < 1 - μ) :
      t 0 = (1 - μ) / (t 0 + μ) ^ 2 - μ / (1 - μ - t 0) ^ 2 := by
    have hr : 0 < t 0 + μ := by linarith
    have hd : 0 < 1 - μ - t 0 := by linarith
    have hn : t 0 - 1 + μ < 0 := by linarith
    have hroot₁ : Real.sqrt ((t 0 + μ) ^ 2 + (t 1) ^ 2) = t 0 + μ := by
      simp [ha, Real.sqrt_sq_eq_abs, abs_of_pos hr]
    have hroot₂ : Real.sqrt ((t 0 - 1 + μ) ^ 2 + (t 1) ^ 2) =
        1 - μ - t 0 := by
      calc
        _ = |t 0 - 1 + μ| := by simp [ha, Real.sqrt_sq_eq_abs]
        _ = 1 - μ - t 0 := by rw [abs_of_neg hn]; ring
    have hzero : partialDerivative (jacobiHamiltonian μ) t 0 = 0 := by
      simp [partialDerivative, hc.2]
    have hmom := (jacobi_critical_momentum μ t hc).2
    have hder := jacobi_partial_position_one μ t hf
    rw [hzero, hmom, hroot₁, hroot₂] at hder
    have h₁ : (1 - μ) * (t 0 + μ) / (t 0 + μ) ^ 3 =
        (1 - μ) / (t 0 + μ) ^ 2 := by
      have hne : t 0 + μ ≠ 0 := ne_of_gt hr
      field_simp
    have h₂ : μ * (t 0 - 1 + μ) / (1 - μ - t 0) ^ 3 =
        -(μ / (1 - μ - t 0) ^ 2) := by
      have hne : 1 - μ - t 0 ≠ 0 := ne_of_gt hd
      field_simp
      ring
    rw [h₁, h₂] at hder
    linarith
  rcases hL with ⟨hLfree, hLcrit, hLleft, hLright, hLaxis⟩
  have hbL := balance L hLfree hLcrit hLaxis hLleft hLright
  have hbs := balance s hfree hcrit haxis hleft hright
  by_contra hne
  have hne' : L 0 ≠ s 0 := by intro h; exact hne h.symm
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have hr₁ : 0 < L 0 + μ := by linarith
    have hr₂ : 0 < s 0 + μ := by linarith
    have hd₁ : 0 < 1 - μ - L 0 := by linarith
    have hd₂ : 0 < 1 - μ - s 0 := by linarith
    have hsq₁ : (L 0 + μ) ^ 2 < (s 0 + μ) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hr₁ hr₂)]
    have hsq₂ : (1 - μ - s 0) ^ 2 < (1 - μ - L 0) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hd₁ hd₂)]
    have hrrec := one_div_lt_one_div_of_lt (sq_pos_of_pos hr₁) hsq₁
    have hdrec := one_div_lt_one_div_of_lt (sq_pos_of_pos hd₂) hsq₂
    have hmul₁ := mul_lt_mul_of_pos_left hrrec (sub_pos.mpr hμ1)
    have hmul₂ := mul_lt_mul_of_pos_left hdrec hμ0
    simp only [one_div, div_eq_mul_inv] at hbL hbs hmul₁ hmul₂
    linarith
  · have hr₁ : 0 < L 0 + μ := by linarith
    have hr₂ : 0 < s 0 + μ := by linarith
    have hd₁ : 0 < 1 - μ - L 0 := by linarith
    have hd₂ : 0 < 1 - μ - s 0 := by linarith
    have hsq₁ : (s 0 + μ) ^ 2 < (L 0 + μ) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hgt) (add_pos hr₁ hr₂)]
    have hsq₂ : (1 - μ - L 0) ^ 2 < (1 - μ - s 0) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hgt) (add_pos hd₁ hd₂)]
    have hrrec := one_div_lt_one_div_of_lt (sq_pos_of_pos hr₂) hsq₁
    have hdrec := one_div_lt_one_div_of_lt (sq_pos_of_pos hd₁) hsq₂
    have hmul₁ := mul_lt_mul_of_pos_left hrrec (sub_pos.mpr hμ1)
    have hmul₂ := mul_lt_mul_of_pos_left hdrec hμ0
    simp only [one_div, div_eq_mul_inv] at hbL hbs hmul₁ hmul₂
    linarith
