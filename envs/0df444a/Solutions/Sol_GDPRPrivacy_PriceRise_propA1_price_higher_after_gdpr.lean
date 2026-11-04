-- Prove2me | solution 1 for GDPRPrivacy.PriceRise.propA1_price_higher_after_gdpr
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:28:43.173367+00:00
-- url     : https://prove2.me/submissions/9501036d-d58f-4ff4-99a9-cc1dce6bc823

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model
import Theorems.Thm_GDPRPrivacy_PriceRise_oaD_price_gap

open GDPRPrivacy.PriceRise

theorem solution (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) :
    (∃ p, IsMaxOn (profitBefore x α) Set.univ p) ∧
    (∃ p, IsMaxOn (profitAfter x α) Set.univ p) ∧
    ∀ pHat pTilde : ℝ,
      IsMaxOn (profitBefore x α) Set.univ pHat →
      IsMaxOn (profitAfter x α) Set.univ pTilde →
        pHat < pTilde := by
  obtain ⟨hE1, hE2, hgap⟩ := oaD_price_gap x α hx0 hx1 hα
  refine ⟨hE1, hE2, fun pHat pTilde hH hT => ?_⟩
  obtain ⟨g1, g2, g3⟩ := hgap pHat pTilde hH hT
  have hβ0 : 0 ≤ beta x α := Real.sqrt_nonneg _
  have hβsq : beta x α ^ 2 = 6 + (x + α - 1) ^ 2 := Real.sq_sqrt (by positivity)
  have hΓ0 : 0 ≤ Gamma x α := Real.sqrt_nonneg _
  have hΓsq : Gamma x α ^ 2 = 6 + (2 - 2 * x + α) ^ 2 := Real.sq_sqrt (by positivity)
  by_cases hA1 : α < alpha1 x
  · -- region I: x < 1/2
    have h1 : α < (1 - 2 * x) / 2 := by
      unfold alpha1 at hA1
      rcases max_cases ((1 - 2 * x) / 2) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hA1 <;> linarith
    have := g1 hA1
    nlinarith [mul_nonneg hα hx0.le]
  · rw [not_lt] at hA1
    have h1 : (1 - 2 * x) / 2 ≤ α := le_trans (le_max_left _ _) hA1
    by_cases hA2 : α < alpha2 x
    · have h2 : 2 * x * α < 2 - 4 * x + x ^ 2 := by
        unfold alpha2 at hA2
        rcases max_cases ((2 - 4 * x + x ^ 2) / (2 * x)) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hA2
        · rw [lt_div_iff₀ (by positivity)] at hA2; linarith
        · linarith
      have := g2 hA1 hA2
      have hL : 0 < 14 + 4 * α + 3 * x ^ 2 - 8 * x - 6 * x * α := by nlinarith
      have hP : 0 < 12*α^2*x^2 - 16*α^2*x - 12*α*x^3 + 40*α*x^2 - 88*α*x + 48*α + 3*x^4
          - 16*x^3 + 44*x^2 - 64*x + 28 := by
        nlinarith [mul_pos hx0 (sub_pos.2 hx1), mul_nonneg hα hx0.le,
          mul_nonneg (mul_nonneg hα hα) hx0.le, sub_pos.2 h2,
          mul_pos (sub_pos.2 h2) (sub_pos.2 hx1), mul_nonneg hα (sub_pos.2 h2).le]
      have hLβ : 4 * beta x α < 14 + 4 * α + 3 * x ^ 2 - 8 * x - 6 * x * α := by
        nlinarith
      linarith
    · rw [not_lt] at hA2
      have := g3 hA2
      have hlt : beta x α < Gamma x α := by
        nlinarith [mul_pos (sub_pos.2 hx1) (sub_pos.2 hx1), mul_nonneg hα (sub_pos.2 hx1).le]
      linarith
