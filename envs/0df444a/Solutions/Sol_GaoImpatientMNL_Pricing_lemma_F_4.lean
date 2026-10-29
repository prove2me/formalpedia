-- Prove2me | solution 1 for GaoImpatientMNL.Pricing.lemma_F_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:03:13.172867+00:00
-- url     : https://prove2.me/submissions/94c53bf3-b6de-4ba0-9a85-f80637e75e1f

import Mathlib

theorem solution (s t : ℝ) (hs : 1 < s) (ht : 1 < t)
    (h : Real.log (s * t) + 1 / t - s = 0) : 2 - 1 / t ≤ s := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < s := by linarith
  -- log (2t-1) ≥ 2(t-1)/t from the first term of the artanh series
  have key : 2 * (t - 1) / t ≤ Real.log (2 * t - 1) := by
    have ha : 0 < 1 / (2 * (t - 1)) := by apply div_pos one_pos; linarith
    have hs' := Real.hasSum_log_one_add_inv ha
    have e1 : 1 + (1 / (2 * (t - 1)))⁻¹ = 2 * t - 1 := by
      rw [one_div, inv_inv]; ring
    rw [e1] at hs'
    have := le_hasSum hs' 0 (fun j _ => by positivity)
    have e2 : (2 : ℝ) * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * (1 / (2 * (1 / (2 * (t - 1))) + 1)) ^ (2 * 0 + 1)
        = 2 * (t - 1) / t := by
      have : t - 1 ≠ 0 := by linarith
      have : t ≠ 0 := ht0.ne'
      have h3 : (2:ℝ) * (1 / (2 * (t - 1))) + 1 = t / (t - 1) := by field_simp; ring
      rw [h3]; norm_num
      field_simp
    linarith [e2 ▸ this]
  by_contra hlt
  push Not at hlt
  set c := 2 - 1 / t with hc
  have hc1 : 1 < c := lt_trans hs hlt
  have hc0 : 0 < c := by linarith
  have hlogcs : Real.log c - Real.log s < c - s := by
    rw [← Real.log_div hc0.ne' hs0.ne']
    have h1 := Real.log_lt_sub_one_of_pos (div_pos hc0 hs0) (by
      intro heq; rw [div_eq_one_iff_eq hs0.ne'] at heq; linarith)
    have h2 : c / s - 1 ≤ c - s := by
      rw [div_sub_one hs0.ne', div_le_iff₀ hs0]; nlinarith
    linarith
  have hct : Real.log c + Real.log t = Real.log (2 * t - 1) := by
    rw [← Real.log_mul hc0.ne' ht0.ne']; congr 1; rw [hc]; field_simp
  rw [Real.log_mul hs0.ne' ht0.ne'] at h
  have e3 : 2 * (t - 1) / t = 2 - 2 * (1 / t) := by field_simp
  linarith

