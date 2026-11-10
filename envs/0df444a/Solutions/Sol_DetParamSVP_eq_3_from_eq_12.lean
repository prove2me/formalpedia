-- Prove2me | solution 1 for DetParamSVP.eq_3_from_eq_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:59:58.892683+00:00
-- url     : https://prove2.me/submissions/d36f3730-a6bf-4661-98bd-4ccde7a413c5

import Mathlib

set_option autoImplicit false

theorem solution (p : ℝ) (hp : 1 ≤ p) (γ c d h k : ℕ) (hγ : 2 ≤ γ) (hc : 1 ≤ c)
    (hγc : (γ : ℝ) ^ p / 2 + 8 ≤ (c : ℝ) ^ p) (hd : 1 ≤ d)
    (hh₁ : (d : ℝ) ^ p ≤ h) (hh₂ : (h : ℝ) < (d : ℝ) ^ p + 3 / 2)
    (hk₁ : ((γ * d : ℕ) : ℝ) ^ p / 2 < k) (hk₂ : (k : ℝ) < ((γ * d : ℕ) : ℝ) ^ p / 2 + 3 / 2) :
    2 ≤ γ * d ∧ 2 ≤ k ∧ ((γ * d : ℕ) : ℝ) ^ p < 2 * k ∧ (d : ℝ) ^ p ≤ h ∧
      (d : ℝ) ^ p + ((k : ℝ) - 1 + 2 * h) + 1 < ((γ * d : ℕ) : ℝ) ^ p / 2 + 3 * (d : ℝ) ^ p + 9 / 2 ∧
      ((γ * d : ℕ) : ℝ) ^ p / 2 + 3 * (d : ℝ) ^ p + 9 / 2 ≤ ((γ : ℝ) ^ p / 2 + 8) * (d : ℝ) ^ p ∧
      ((γ : ℝ) ^ p / 2 + 8) * (d : ℝ) ^ p ≤ ((c * d : ℕ) : ℝ) ^ p := by
  have hγR : (2 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hD : 1 ≤ (d : ℝ) ^ p := Real.one_le_rpow hdR (by linarith)
  have hG : (2 : ℝ) ≤ (γ : ℝ) ^ p := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ γ) hp
    rw [Real.rpow_one] at this
    linarith
  have hGD : ((γ * d : ℕ) : ℝ) ^ p = (γ : ℝ) ^ p * (d : ℝ) ^ p := by
    push_cast
    exact Real.mul_rpow (by linarith) (by linarith)
  have hCD : ((c * d : ℕ) : ℝ) ^ p = (c : ℝ) ^ p * (d : ℝ) ^ p := by
    push_cast
    exact Real.mul_rpow (by linarith) (by linarith)
  have hGD2 : 2 ≤ ((γ * d : ℕ) : ℝ) ^ p := by
    rw [hGD]; nlinarith
  refine ⟨?_, ?_, by linarith, hh₁, by linarith, ?_, ?_⟩
  · nlinarith
  · have : (1 : ℝ) < k := by linarith
    have : 1 < k := by exact_mod_cast this
    omega
  · rw [hGD]; nlinarith
  · rw [hCD]
    exact mul_le_mul_of_nonneg_right hγc (by linarith)
