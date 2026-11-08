-- Prove2me | solution 1 for BankLiability.lambda_root
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:27:03.912604+00:00
-- url     : https://prove2.me/submissions/ac6ad2d2-77e7-4a86-9df2-ef140ce29563

import Mathlib
import Definitions.Def_BankLiability_Params
import Definitions.Def_BankLiability_lam

open BankLiability in
theorem solution (P : Params) :
    0 < lam P ∧
    P.sigma ^ 2 * lam P * (1 + lam P) / 2 - (P.r - P.delta) * lam P - P.r = 0 ∧
    (∀ x : ℝ, 0 < x →
      P.sigma ^ 2 * x * (1 + x) / 2 - (P.r - P.delta) * x - P.r = 0 → x = lam P) ∧
    (P.delta = 0 → lam P = 2 * P.r / P.sigma ^ 2) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = P.sigma ^ 2 / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = P.sigma ^ 2 / 2 - (P.r - P.delta) := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (b ^ 2 + 4 * a * P.r) := ⟨_, rfl⟩
  have hlam : lam P = (-b + s) / (2 * a) := by rw [hsdef, ha, hb]; rfl
  have hσ := P.sigma_pos
  have hr := P.r_pos
  have ha0 : 0 < a := by rw [ha]; positivity
  have hD : 0 ≤ b ^ 2 + 4 * a * P.r := by positivity
  have hs2 : s ^ 2 = b ^ 2 + 4 * a * P.r := by rw [hsdef]; exact Real.sq_sqrt hD
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg _
  have hsb : b < s := by
    by_contra h
    push_neg at h
    have h1 : s * s ≤ b * b := mul_le_mul h h hs0 (le_trans hs0 h)
    nlinarith [mul_pos ha0 hr]
  have hf : ∀ x : ℝ, P.sigma ^ 2 * x * (1 + x) / 2 - (P.r - P.delta) * x - P.r =
      a * x ^ 2 + b * x - P.r := by
    intro x; rw [ha, hb]; ring
  have hpos : 0 < (-b + s) / (2 * a) := div_pos (by linarith) (by linarith)
  have hroot : a * ((-b + s) / (2 * a)) ^ 2 + b * ((-b + s) / (2 * a)) - P.r = 0 := by
    have e : a * ((-b + s) / (2 * a)) ^ 2 + b * ((-b + s) / (2 * a)) - P.r =
        (s ^ 2 - (b ^ 2 + 4 * a * P.r)) / (4 * a) := by
      have := ha0.ne'
      first | (field_simp; ring) | field_simp
    rw [e, hs2, sub_self, zero_div]
  refine ⟨by rw [hlam]; exact hpos, by rw [hf, hlam]; exact hroot, ?_, ?_⟩
  · intro x hx hxr
    rw [hf] at hxr
    rw [hlam]
    obtain ⟨l, hl⟩ : ∃ l, l = (-b + s) / (2 * a) := ⟨_, rfl⟩
    rw [← hl] at hroot hpos ⊢
    have hfac : (x - l) * (a * (x + l) + b) = 0 := by linear_combination hxr - hroot
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · exfalso
      have h3 : a * x * l = -P.r := by linear_combination l * h - hroot
      have h4 : 0 < a * x * l := by positivity
      linarith
  · intro hδ
    have hb' : b = a - P.r := by rw [hb, ha, hδ]; ring
    have hs' : s = a + P.r := by
      rw [hsdef, hb', show (a - P.r) ^ 2 + 4 * a * P.r = (a + P.r) ^ 2 by ring,
        Real.sqrt_sq (by linarith)]
    have hσ2 : P.sigma ^ 2 = 2 * a := by rw [ha]; ring
    rw [hlam, hs', hb', hσ2]
    have := ha0.ne'
    first | (field_simp; ring) | field_simp
