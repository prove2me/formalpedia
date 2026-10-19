-- Prove2me | solution 1 for BalancedPrices.WeakExtension.case_2_constant
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:29:34.085897+00:00
-- url     : https://prove2.me/submissions/af457c7b-1069-4593-bc1d-ab40561c12e3

import Mathlib

set_option autoImplicit false

theorem solution (α β₁ β₂ : ℝ) (hα : 0 < α) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hsum : 1 / α ≤ β₁ + β₂) (hcase : β₂ < 1 / (2 * α)) :
    1 / (α * (2 * β₁ + 4 * β₂)) ≤ (1 - α * β₂) / (1 + α * β₁) := by
  rw [div_le_iff₀ hα] at hsum
  rw [lt_div_iff₀ (by positivity)] at hcase
  set u := α * β₁ with hu
  set v := α * β₂ with hv
  have hu0 : 0 ≤ u := by positivity
  have hv0 : 0 ≤ v := by positivity
  have hs : 1 ≤ u + v := by
    have : (β₁ + β₂) * α = u + v := by rw [hu, hv]; ring
    linarith
  have hc : 2 * v < 1 := by
    have : β₂ * (2 * α) = 2 * v := by rw [hv]; ring
    linarith
  have hpos : 0 < α * (2 * β₁ + 4 * β₂) := by
    have : α * (2 * β₁ + 4 * β₂) = 2 * u + 4 * v := by rw [hu, hv]; ring
    rw [this]; linarith
  have hpos2 : 0 < 1 + α * β₁ := by positivity
  rw [div_le_div_iff₀ hpos hpos2]
  have e : (1 - α * β₂) * (α * (2 * β₁ + 4 * β₂)) = (1 - v) * (2 * u + 4 * v) := by
    rw [hu, hv]; ring
  rw [e, one_mul]
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 hc.le), mul_nonneg hv0 (sub_nonneg.2 hc.le)]
