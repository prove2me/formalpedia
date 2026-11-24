-- Prove2me | solution 1 for BB6Kit.numerics
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T22:18:10.392858+00:00
-- url     : https://prove2.me/submissions/b25d8e40-2dac-42b4-a8a7-f0033b6e3cdc

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

theorem solution (i : ℕ) (hi : 2 ^ 60 ≤ i) :
    Real.log ((i : ℝ) + 5) + 2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3 < (i : ℝ) * Real.log 3 := by
  have hx : (2:ℝ) ^ 60 ≤ (i : ℝ) := by exact_mod_cast hi
  set x : ℝ := (i : ℝ) with hxdef
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h4x : 0 ≤ 4 * x := by positivity
  set u : ℝ := (4 * x) ^ ((1:ℝ) / 16) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by positivity) _
  have hu16 : u ^ 16 = 4 * x := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul h4x]
    norm_num
  have hlogb : ∀ y : ℝ, 0 ≤ y → y ≤ 4 * x → Real.log y ≤ 16 * u := by
    intro y hy0 hy
    have h1 := Real.log_le_rpow_div hy0 (by norm_num : (0:ℝ) < 1 / 16)
    have h2 : y ^ ((1:ℝ) / 16) ≤ u := Real.rpow_le_rpow hy0 hy (by norm_num)
    have h3 : y ^ ((1:ℝ) / 16) / (1 / 16) = 16 * y ^ ((1:ℝ) / 16) := by ring
    linarith
  have hL1 := hlogb (x + 5) (by positivity) (by linarith)
  have hL3 := hlogb (4 * x) h4x le_rfl
  have hL3nn : 0 ≤ Real.log (4 * x) := Real.log_nonneg (by linarith)
  have hl : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
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
  have hcube : Real.log (4 * x) ^ 3 ≤ (16 * u) ^ 3 := pow_le_pow_left₀ hL3nn hL3 3
  have h13 : (14:ℝ) ^ 13 ≤ u ^ 13 := pow_le_pow_left₀ (by norm_num) hu14 13
  have hu3 : 0 < u ^ 3 := by positivity
  have hxu : x * Real.log 3 = u ^ 3 * (u ^ 13 * Real.log 3 / 4) := by
    have : x = u ^ 16 / 4 := by rw [hu16]; ring
    rw [this]; ring
  have key : 16 * u + 2 ^ 30 * (16 * u) ^ 3 < u ^ 3 * (u ^ 13 * Real.log 3 / 4) := by
    have e1 : 2 ^ 30 * (16 * u) ^ 3 = 2 ^ 42 * u ^ 3 := by ring
    have hu2 : (16:ℝ) ≤ u ^ 2 := by nlinarith
    have e2 : 16 * u ≤ u ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hu2 hu0.le
      calc 16 * u = u * 16 := by ring
        _ ≤ u * u ^ 2 := h
        _ = u ^ 3 := by ring
    have e3 : (14:ℝ) ^ 13 * 1 / 4 ≤ u ^ 13 * Real.log 3 / 4 := by
      have := mul_le_mul h13 hl.le (by norm_num) (by positivity)
      linarith
    have e4 : (1 + 2 ^ 42 : ℝ) < 14 ^ 13 * 1 / 4 := by norm_num
    have e5 : u ^ 3 * (1 + 2 ^ 42) < u ^ 3 * (u ^ 13 * Real.log 3 / 4) :=
      mul_lt_mul_of_pos_left (lt_of_lt_of_le e4 e3) hu3
    nlinarith
  have := mul_le_mul_of_nonneg_left hcube (by positivity : (0:ℝ) ≤ 2 ^ 30)
  rw [hxu]
  linarith
