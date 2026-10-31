-- Prove2me | solution 1 for BrandLicensing.Intensive.eq_12_licensee_effort
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:01:13.54431+00:00
-- url     : https://prove2.me/submissions/c8a588ae-5c47-4550-bf2f-9d71d13269f2

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model
open BrandLicensing.Intensive

theorem solution(P : Params) (hP : P.Standing) (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (e : ℝ) (he : 0 ≤ e) :
    (∀ e', 0 ≤ e' → piLicensee P c s e' ≤ piLicensee P c s e) ↔ e = eE12 P c s := by
  obtain ⟨hα0, hα1, hθ, hμ, hρ0, hρ1, hl0, hl1, hε⟩ := hP
  have h2r : (2 - P.ρ) ≠ 0 := by linarith
  have hcpos : 0 < 1 / 2 - P.ρ / 4 := by linarith
  have gap : ∀ e', 0 ≤ e' → (1 / 2 - P.ρ / 4) * (e' - eE12 P c s) ^ 2 ≤ piLicensee P c s (eE12 P c s) - piLicensee P c s e' := by
    intro e' he'
    unfold piLicensee piM eE12
    rcases le_or_gt 0 ((1 - P.α) * c - s) with hk | hk
    · rw [max_eq_left hk]
      have hE0 : 0 ≤ P.ρ / (2 - P.ρ) * ((1 - P.α) * c - s) := mul_nonneg (div_nonneg hρ0 (by linarith)) hk
      rw [max_eq_left (by linarith : 0 ≤ P.ρ / (2 - P.ρ) * ((1 - P.α) * c - s) + (1 - P.α) * c - s),
        max_eq_left (by linarith : 0 ≤ e' + (1 - P.α) * c - s)]
      have hstar : (2 - P.ρ) * (P.ρ / (2 - P.ρ) * ((1 - P.α) * c - s)) = P.ρ * ((1 - P.α) * c - s) := by
        field_simp
      apply le_of_eq
      linear_combination ((P.ρ / (2 - P.ρ) * ((1 - P.α) * c - s) - e') / 2) * hstar
    · rw [max_eq_right hk.le, mul_zero]
      rw [max_eq_right (by linarith : (0:ℝ) + (1 - P.α) * c - s ≤ 0)]
      rcases le_or_gt (e' + (1 - P.α) * c - s) 0 with h1 | h1
      · rw [max_eq_right h1]; nlinarith [sq_nonneg e', mul_nonneg hρ0 (sq_nonneg e')]
      · rw [max_eq_left h1.le]
        have : (e' + (1 - P.α) * c - s) ^ 2 ≤ e' ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this hρ0, mul_nonneg hρ0 (sq_nonneg e')]
  constructor
  · intro hmax
    have h1 := hmax (eE12 P c s) (by unfold eE12; exact mul_nonneg (div_nonneg hρ0 (by linarith)) (le_max_right _ _))
    have h2 := gap e he
    have h3 : (e - eE12 P c s) ^ 2 = 0 := by
      nlinarith [sq_nonneg (e - eE12 P c s), mul_nonneg hcpos.le (sq_nonneg (e - eE12 P c s))]
    have := pow_eq_zero_iff two_ne_zero |>.mp h3
    linarith
  · rintro rfl e' he'
    have := gap e' he'
    nlinarith [mul_nonneg hcpos.le (sq_nonneg (e' - eE12 P c s))]
