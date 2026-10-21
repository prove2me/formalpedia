-- Prove2me | solution 1 for ClimateImpact.Interaction.foc_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:05:30.596183+00:00
-- url     : https://prove2.me/submissions/9dc12252-6613-425f-b4ed-d391becad873

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 ≤ ε) (a x : Fin n → ℝ)
    (h : ∀ i, x i = a i - ε / (2 * n) * (∑ j, x j + x i)) :
    ∑ i, x i = 2 * n / (2 * n + (n + 1) * ε) * ∑ i, a i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ i, x i = ∑ i, a i - ε / (2 * n) * (n * ∑ j, x j + ∑ i, x i) := by
    calc ∑ i, x i = ∑ i, (a i - ε / (2 * n) * (∑ j, x j + x i)) := Finset.sum_congr rfl (fun i _ => h i)
      _ = ∑ i, a i - ε / (2 * n) * (∑ i, (∑ j, x j + x i)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp
  have hd : (0 : ℝ) < 2 * n + (n + 1) * ε := by positivity
  have h2 : 2 * n * ∑ i, x i = 2 * n * ∑ i, a i - ε * (n * ∑ j, x j + ∑ i, x i) := by
    have e : 2 * (n : ℝ) * (ε / (2 * n) * (n * ∑ j, x j + ∑ i, x i)) = ε * (n * ∑ j, x j + ∑ i, x i) := by
      field_simp
    calc 2 * (n : ℝ) * ∑ i, x i = 2 * n * (∑ i, a i - ε / (2 * n) * (n * ∑ j, x j + ∑ i, x i)) := by
          rw [← hsum]
      _ = _ := by rw [mul_sub, e]
  rw [div_mul_eq_mul_div, eq_div_iff hd.ne']
  linarith
