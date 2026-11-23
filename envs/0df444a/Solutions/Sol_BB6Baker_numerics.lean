-- Prove2me | solution 1 for BB6Baker.numerics
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T17:59:56.353996+00:00
-- url     : https://prove2.me/submissions/1f3a68d0-b1ae-4bb5-976d-081fdb0cdde2

import Mathlib

theorem solution (i : ℕ) (hi : 2 ^ 60 ≤ i) :
    Real.log ((i : ℝ) + 5) + 2 ^ 42 * Real.log (2 * (i : ℝ) + 2) * Real.log 3 * Real.log (4 * (i : ℝ)) <
      (i : ℝ) * Real.log 3 := by
  have hx : (2:ℝ) ^ 60 ≤ (i : ℝ) := by exact_mod_cast hi
  set x : ℝ := (i : ℝ) with hxdef
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h4x : 0 ≤ 4 * x := by positivity
  -- u = (4x)^(1/16)
  set u : ℝ := (4 * x) ^ ((1:ℝ) / 16) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by positivity) _
  have hu16 : u ^ 16 = 4 * x := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul h4x]
    norm_num
  -- logarithm bounds: log y ≤ 16 * u for 1 ≤ y ≤ 4x
  have hlogb : ∀ y : ℝ, 0 ≤ y → y ≤ 4 * x → Real.log y ≤ 16 * u := by
    intro y hy0 hy
    have h1 := Real.log_le_rpow_div hy0 (by norm_num : (0:ℝ) < 1 / 16)
    have h2 : y ^ ((1:ℝ) / 16) ≤ u := Real.rpow_le_rpow hy0 hy (by norm_num)
    have h3 : y ^ ((1:ℝ) / 16) / (1 / 16) = 16 * y ^ ((1:ℝ) / 16) := by ring
    linarith
  have hL1 := hlogb (x + 5) (by positivity) (by linarith)
  have hL2 := hlogb (2 * x + 2) (by positivity) (by linarith)
  have hL3 := hlogb (4 * x) h4x le_rfl
  have hL2nn : 0 ≤ Real.log (2 * x + 2) := Real.log_nonneg (by linarith)
  have hL3nn : 0 ≤ Real.log (4 * x) := Real.log_nonneg (by linarith)
  -- log 3 > 1
  have hl : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hl0 : 0 < Real.log 3 := by linarith
  -- u ≥ 14
  have hu14 : 14 ≤ u := by
    by_contra h
    push_neg at h
    have : u ^ 16 < 14 ^ 16 := pow_lt_pow_left₀ h hu0.le (by norm_num)
    rw [hu16] at this
    have : (2:ℝ) ^ 62 ≤ 4 * x := by
      have : (2:ℝ) ^ 62 = 4 * 2 ^ 60 := by norm_num
      linarith
    norm_num at *
    linarith
  have h14 : (14:ℝ) ^ 14 ≤ u ^ 14 := pow_le_pow_left₀ (by norm_num) hu14 14
  -- product bound
  have hprod : 2 ^ 42 * Real.log (2 * x + 2) * Real.log 3 * Real.log (4 * x) ≤
      2 ^ 50 * Real.log 3 * u ^ 2 := by
    have a1 : Real.log (2 * x + 2) * Real.log (4 * x) ≤ (16 * u) * (16 * u) :=
      mul_le_mul hL2 hL3 hL3nn (by positivity)
    have a2 : 2 ^ 42 * Real.log 3 * (Real.log (2 * x + 2) * Real.log (4 * x)) ≤
        2 ^ 42 * Real.log 3 * ((16 * u) * (16 * u)) :=
      mul_le_mul_of_nonneg_left a1 (by positivity)
    nlinarith [a2]
  -- final comparison
  have hq : 16 * u ≤ 2 * u ^ 2 := by nlinarith
  have key : 2 + 2 ^ 50 * Real.log 3 < 14 ^ 14 * Real.log 3 / 4 := by
    norm_num
    nlinarith
  have hu2 : 0 < u ^ 2 := by positivity
  have k2 := mul_lt_mul_of_pos_left key hu2
  have k3 : u ^ 2 * (14 ^ 14 * Real.log 3 / 4) ≤ u ^ 2 * (u ^ 14 * Real.log 3 / 4) := by
    apply mul_le_mul_of_nonneg_left _ hu2.le
    have := mul_le_mul_of_nonneg_right h14 hl0.le
    linarith
  have hxu : x * Real.log 3 = u ^ 2 * (u ^ 14 * Real.log 3 / 4) := by
    have : x = u ^ 16 / 4 := by rw [hu16]; ring
    rw [this]; ring
  rw [hxu]
  nlinarith [hL1, hprod, hq, k2, k3]
