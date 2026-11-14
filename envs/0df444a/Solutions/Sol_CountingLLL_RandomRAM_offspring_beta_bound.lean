-- Prove2me | solution 1 for CountingLLL.RandomRAM.offspring_beta_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:06:35.779292+00:00
-- url     : https://prove2.me/submissions/42cbac4f-6ee8-44e0-9c26-6096630f9367

import Mathlib
set_option autoImplicit false

/-- The numerical offspring contraction in #442 Lemma 5.7. -/
theorem offspring_beta_bound (p D : ℝ) (hp : 0 ≤ p) (hD : 1 ≤ D)
    (hcondition : 4 * Real.exp 1 * p * (D+1)^2 ≤ 1) :
    p * (D+1)^2 / ((1-p) * (1-p*D^2)) ≤ 40/351 ∧
    p * (D+1)^2 / ((1-p) * (1-p*D^2)) < 1/8 := by
  have hcoef : (10 : ℝ) ≤ 4 * Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hA0 : 0 ≤ p * (D+1)^2 := mul_nonneg hp (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hcoef hA0
  have hA : p * (D+1)^2 ≤ 1/10 := by nlinarith
  have hD2 : (4 : ℝ) ≤ (D+1)^2 := by nlinarith
  have hp4 := mul_le_mul_of_nonneg_left hD2 hp
  have hp40 : p ≤ 1/40 := by nlinarith
  have hDle : D^2 ≤ (D+1)^2 := by nlinarith
  have hpD := mul_le_mul_of_nonneg_left hDle hp
  have hB : p*D^2 ≤ 1/10 := by linarith
  have h1 : (39/40 : ℝ) ≤ 1-p := by linarith
  have h2 : (9/10 : ℝ) ≤ 1-p*D^2 := by linarith
  have hden : (351/400 : ℝ) ≤ (1-p)*(1-p*D^2) := by
    nlinarith [mul_nonneg (show 0 ≤ (1-p)-(39/40 : ℝ) by linarith)
      (show 0 ≤ (1-p*D^2)-(9/10 : ℝ) by linarith)]
  have hdenpos : 0 < (1-p)*(1-p*D^2) := by linarith
  have hβ : p * (D+1)^2 / ((1-p)*(1-p*D^2)) ≤ 40/351 := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith
  exact ⟨hβ, hβ.trans_lt (by norm_num)⟩

theorem solution (p D : ℝ) (hp : 0 ≤ p) (hD : 1 ≤ D)
    (hcondition : 4 * Real.exp 1 * p * (D+1)^2 ≤ 1) :
    0 ≤ p * (D+1)^2 / ((1-p) * (1-p*D^2)) ∧
    p * (D+1)^2 / ((1-p) * (1-p*D^2)) ≤ 40/351 ∧
    p * (D+1)^2 / ((1-p) * (1-p*D^2)) < 1/8 := by
  have hcoef : (10 : ℝ) ≤ 4 * Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hA0 : 0 ≤ p * (D+1)^2 := mul_nonneg hp (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hcoef hA0
  have hA : p * (D+1)^2 ≤ 1/10 := by nlinarith
  have hD2 : (4 : ℝ) ≤ (D+1)^2 := by nlinarith
  have hp4 := mul_le_mul_of_nonneg_left hD2 hp
  have hp40 : p ≤ 1/40 := by nlinarith
  have hDle : D^2 ≤ (D+1)^2 := by nlinarith
  have hpD := mul_le_mul_of_nonneg_left hDle hp
  have hB : p*D^2 ≤ 1/10 := by linarith
  have hden : 0 ≤ (1-p)*(1-p*D^2) := mul_nonneg (by linarith) (by linarith)
  exact ⟨div_nonneg hA0 hden, offspring_beta_bound p D hp hD hcondition⟩
