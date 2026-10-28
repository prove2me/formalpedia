-- Prove2me | solution 1 for EndoCredit.Baseline.alpha_plus_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:40:15.841695+00:00
-- url     : https://prove2.me/submissions/f091cb58-c733-4a67-a58f-66f4332f04a3

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

open EndoCredit.Baseline in
theorem solution (p : Params) (hp : p.Standing) :
    1 < alphaPlus p ∧
    quadA p * alphaPlus p * (alphaPlus p - 1) +
      (betaHat p - rI p) * alphaPlus p - betaHat p = 0 ∧
    ∀ a : ℝ, 0 < a →
      quadA p * a * (a - 1) + (betaHat p - rI p) * a - betaHat p = 0 →
      a = alphaPlus p := by
  obtain ⟨⟨_, _, _, _, _, _, _, hR, _, hB, hA, _⟩, _, _⟩ := hp
  have hap : alphaPlus p = (-(betaHat p - rI p - quadA p) +
      Real.sqrt ((betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p)) /
      (2 * quadA p) := rfl
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt ((betaHat p - rI p - quadA p) ^ 2 +
      4 * quadA p * betaHat p) := ⟨_, rfl⟩
  have hD : 0 ≤ (betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p := by positivity
  have hs2 : s ^ 2 = (betaHat p - rI p - quadA p) ^ 2 + 4 * quadA p * betaHat p := by
    rw [hs]; exact Real.sq_sqrt hD
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  rw [← hs] at hap
  obtain ⟨x, hxdef⟩ : ∃ x, x = alphaPlus p := ⟨_, rfl⟩
  rw [← hxdef]
  have hx : 2 * quadA p * x = s - (betaHat p - rI p - quadA p) := by
    rw [hxdef, hap]; field_simp; ring
  have hAB : 0 < quadA p * betaHat p := mul_pos hA hB
  refine ⟨?_, ?_, ?_⟩
  · -- s > 2A + b
    have hgt : 2 * quadA p + (betaHat p - rI p - quadA p) < s := by
      by_contra h
      push_neg at h
      nlinarith [mul_self_le_mul_self hs0 h]
    nlinarith
  · have h4 : (4 * quadA p) * (quadA p * x * (x - 1) + (betaHat p - rI p) * x - betaHat p)
        = 0 := by
      linear_combination (2 * quadA p * x + s + (betaHat p - rI p - quadA p)) * hx + hs2
    exact (mul_eq_zero.mp h4).resolve_left (by positivity)
  · intro a ha hGa
    have hGx : quadA p * x * (x - 1) + (betaHat p - rI p) * x - betaHat p = 0 := by
      have h4 : (4 * quadA p) * (quadA p * x * (x - 1) + (betaHat p - rI p) * x - betaHat p)
          = 0 := by
        linear_combination (2 * quadA p * x + s + (betaHat p - rI p - quadA p)) * hx + hs2
      exact (mul_eq_zero.mp h4).resolve_left (by positivity)
    have hsb : 0 < s + (betaHat p - rI p - quadA p) := by
      by_contra h
      push_neg at h
      have h' : s ≤ -(betaHat p - rI p - quadA p) := by linarith
      nlinarith [mul_self_le_mul_self hs0 h']
    have hprod : (a - x) * (2 * quadA p * a + s + (betaHat p - rI p - quadA p)) = 0 := by
      linear_combination 2 * hGa - 2 * hGx - (a - x) * hx
    have hpos : 0 < 2 * quadA p * a + s + (betaHat p - rI p - quadA p) := by
      have := mul_pos hA ha
      linarith
    have := (mul_eq_zero.mp hprod).resolve_right hpos.ne'
    linarith
