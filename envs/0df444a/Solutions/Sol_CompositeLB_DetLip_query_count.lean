-- Prove2me | solution 1 for CompositeLB.DetLip.query_count
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:26:28.93199+00:00
-- url     : https://prove2.me/submissions/e911cd91-7f5b-406a-ab7b-5a60f6529df6

import Mathlib

set_option autoImplicit false

theorem solution (m : ℕ) (ε : ℝ) (hm : 1 ≤ m)
    (hε : 0 < ε) (hε_bound : ε ≤ 1 / 12) :
    (m : ℝ) / (48 * ε) ≤
      min ((m : ℝ) / ε)
        (((⌊1 / (12 * ε)⌋₊ : ℕ) : ℝ) *
          ((⌈(m : ℝ) / 2⌉₊ : ℕ) : ℝ)) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  apply le_min
  · rw [div_le_div_iff₀ (by positivity) hε]
    nlinarith
  · set x : ℝ := 1 / (12 * ε) with hx
    have hx1 : 1 ≤ x := by
      rw [hx, le_div_iff₀ (by positivity)]
      linarith
    have hfl : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
      have h1 := Nat.lt_floor_add_one x
      have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (by simpa using hx1)
      linarith
    have hce : (m : ℝ) / 2 ≤ (⌈(m : ℝ) / 2⌉₊ : ℝ) := Nat.le_ceil _
    have hxe : (m : ℝ) / (48 * ε) = x / 2 * ((m : ℝ) / 2) := by
      rw [hx]; field_simp; ring
    rw [hxe]
    have : 0 ≤ x / 2 := by linarith
    have hmul : x / 2 * ((m : ℝ) / 2) ≤ (⌊x⌋₊ : ℝ) * (⌈(m : ℝ) / 2⌉₊ : ℝ) :=
      mul_le_mul hfl hce (by positivity) (by positivity)
    have : 0 ≤ x / 2 * ((m : ℝ) / 2) := by positivity
    linarith
