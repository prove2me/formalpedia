-- Prove2me | solution 1 for DGPNash.NashMap.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:01:40.29933+00:00
-- url     : https://prove2.me/submissions/cd3e086d-1b2f-43bb-b71f-72aa468efd26

import Mathlib

theorem solution (x x' y y' z z' : ℝ)
    (hx : 0 ≤ x) (hx' : 0 ≤ x') (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (hz : 0 ≤ z) (hz' : 0 ≤ z') (hfrac : (x + y) / (1 + z) ≤ 1) :
    |(x + y) / (1 + z) - (x' + y') / (1 + z')| ≤
      |x - x'| + |y - y'| + |z - z'| := by
  have hz1 : (0:ℝ) < 1 + z := by linarith
  have hz1' : (0:ℝ) < 1 + z' := by linarith
  have hAu : (x + y) / (1 + z) * (1 + z) = x + y := div_mul_cancel₀ _ hz1.ne'
  have hA0 : 0 ≤ (x + y) / (1 + z) := div_nonneg (by linarith) hz1.le
  obtain ⟨A, hA⟩ : ∃ A, A = (x + y) / (1 + z) := ⟨_, rfl⟩
  rw [← hA] at hfrac hAu hA0 ⊢
  have key : A - (x' + y') / (1 + z') =
      ((x - x') + (y - y') + A * (z' - z)) / (1 + z') := by
    rw [eq_div_iff hz1'.ne', sub_mul, div_mul_cancel₀ _ hz1'.ne']
    linear_combination hAu
  rw [key, abs_div, abs_of_pos hz1', div_le_iff₀ hz1']
  have h1 := abs_add_le ((x - x') + (y - y')) (A * (z' - z))
  have h2 := abs_add_le (x - x') (y - y')
  have h3 : |A * (z' - z)| ≤ |z - z'| := by
    rw [abs_mul, abs_of_nonneg hA0, abs_sub_comm]
    exact mul_le_of_le_one_left (abs_nonneg _) hfrac
  have h4 : 0 ≤ |x - x'| + |y - y'| + |z - z'| := by positivity
  nlinarith [mul_nonneg h4 hz']
