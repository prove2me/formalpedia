-- Prove2me | solution 1 for BnBPEP.WeakCvx.eq_46
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:33:11.080511+00:00
-- url     : https://prove2.me/submissions/a7bfbe3d-c27c-4d04-8ae2-90355355ed7e

import Mathlib
set_option autoImplicit false

theorem bernoulli_strict_aux (n : ℕ) (h : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 2) (hn : 1 ≤ n) :
    (1 - 2 * h) ^ n < 1 / (2 * (n : ℝ) * h + 1) := by
  have hx : 0 ≤ (1 - 2 * h) ^ n := pow_nonneg (by linarith) n
  have hpos : 0 < 2 * (n : ℝ) * h + 1 := by positivity
  rw [lt_div_iff₀ hpos]
  have h1 : 1 + (n : ℝ) * (2 * h) ≤ (1 + 2 * h) ^ n :=
    one_add_mul_le_pow (by linarith) n
  have h2 : (1 - 2 * h) ^ n * (1 + (n : ℝ) * (2 * h)) ≤ (1 - 2 * h) ^ n * (1 + 2 * h) ^ n :=
    mul_le_mul_of_nonneg_left h1 hx
  have h3 : (1 - 2 * h) ^ n * (1 + 2 * h) ^ n = (1 - 4 * h ^ 2) ^ n := by
    rw [← mul_pow]; congr 1; ring
  have h4 : (1 - 4 * h ^ 2) ^ n < 1 := by
    apply pow_lt_one₀ (by nlinarith) (by nlinarith) (by omega)
  calc (1 - 2 * h) ^ n * (2 * (n : ℝ) * h + 1)
      = (1 - 2 * h) ^ n * (1 + (n : ℝ) * (2 * h)) := by ring
    _ < 1 := by rw [h3] at h2; exact lt_of_le_of_lt h2 h4

theorem solution (N : ℕ) (h L κ : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 2) (hL : 0 < L) :
    (1 - 2 * h) ^ (N + 1) ≤ 1 / (2 * ((N : ℝ) + 1) * h + 1) ∧
      L ^ 2 / ((N : ℝ) + 1) * (-1 + (1 - 2 * h) ^ (N + 1) + 2 * h * ((N : ℝ) + 1)
          + κ ^ 2 * (2 / h) * (1 - (1 - 2 * h) ^ (N + 1)))
        < L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * ((N : ℝ) + 1) * h + 1)
          + 2 * h * ((N : ℝ) + 1) + κ ^ 2 * (2 / h)) ∧
      L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * ((N : ℝ) + 1) * h + 1)
          + 2 * h * ((N : ℝ) + 1) + κ ^ 2 * (2 / h))
        < L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * ((N : ℝ) + 1) * h)
          + 2 * h * ((N : ℝ) + 1) + κ ^ 2 * (2 / h)) ∧
      L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * ((N : ℝ) + 1) * h)
          + 2 * h * ((N : ℝ) + 1) + κ ^ 2 * (2 / h))
        = L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * h) * (1 / ((N : ℝ) + 1) + 4 * κ ^ 2)
          + 2 * h * ((N : ℝ) + 1)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hB : (1 - 2 * h) ^ (N + 1) < 1 / (2 * ((N : ℝ) + 1) * h + 1) := by
    have := bernoulli_strict_aux (N + 1) h hh0 hh (by omega)
    simpa using this
  have hx : 0 ≤ (1 - 2 * h) ^ (N + 1) := pow_nonneg (by linarith) _
  have hc : 0 < L ^ 2 / ((N : ℝ) + 1) := by positivity
  refine ⟨hB.le, ?_, ?_, ?_⟩
  · apply mul_lt_mul_of_pos_left _ hc
    have : 0 ≤ κ ^ 2 * (2 / h) * (1 - 1 + (1 - 2 * h) ^ (N + 1)) := by
      have : 0 ≤ κ ^ 2 * (2 / h) := by positivity
      simpa using mul_nonneg this hx
    nlinarith
  · apply mul_lt_mul_of_pos_left _ hc
    have : 1 / (2 * ((N : ℝ) + 1) * h + 1) < 1 / (2 * ((N : ℝ) + 1) * h) := by
      apply one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  · congr 1
    field_simp
    ring
