-- Prove2me | solution 1 for Esgk.threshold_failure_fifth_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:52:40.651594+00:00
-- url     : https://prove2.me/submissions/c88b0b00-ed0f-4636-97c2-5e06215cd09a

/-
Standalone solution artifact for Prove2me (mirrors esgk-on3
lean/Esgk/AdditiveExcessArithmetic.lean).-/

import Mathlib

/-- Threshold failure (§16.3, (16.4)): below the `d^(5/2)` threshold,
i.e. `N^2 < C^2 * d^5`, coverage `n * d ≤ N * (2s)` with `d ≤ 2s` forces
`n^2 < 32 * C^2 * s^5` (the `rpow` form `s > n^(2/5)/(2C^(2/5))`
raised to the fifth power). -/
theorem solution (n s N d C : ℕ) (hs : 1 ≤ s)
    (hcov : n * d ≤ N * (2 * s)) (hN : N ^ 2 < C ^ 2 * d ^ 5)
    (hds : d ≤ 2 * s) : n ^ 2 < 32 * C ^ 2 * s ^ 5 := by
  have q1 : (n * d) ^ 2 ≤ (N * (2 * s)) ^ 2 := Nat.pow_le_pow_left hcov 2
  have q2 : (N * (2 * s)) ^ 2 = (N ^ 2) * (4 * (s ^ 2)) := by ring
  have q3 : (N ^ 2) * (4 * (s ^ 2)) < (C ^ 2 * d ^ 5) * (4 * (s ^ 2)) :=
    mul_lt_mul_of_pos_right hN (Nat.mul_pos (by omega) (pow_pos (by omega : 0 < s) 2))
  have q4 : n ^ 2 * (d ^ 2) < (4 * (s ^ 2) * C ^ 2 * (d ^ 3)) * (d ^ 2) := by
    have r1 : (n * d) ^ 2 = n ^ 2 * (d ^ 2) := by ring
    have r2 : (C ^ 2 * d ^ 5) * (4 * (s ^ 2))
        = (4 * (s ^ 2) * C ^ 2 * (d ^ 3)) * (d ^ 2) := by ring
    omega
  have q5 : n ^ 2 < 4 * (s ^ 2) * C ^ 2 * (d ^ 3) := by
    by_contra hc
    have hc' : 4 * (s ^ 2) * C ^ 2 * (d ^ 3) ≤ n ^ 2 := not_lt.mp hc
    have hlt : (4 * (s ^ 2) * C ^ 2 * (d ^ 3)) * (d ^ 2) ≤ (n ^ 2) * (d ^ 2) :=
      mul_le_mul_of_nonneg_right hc' (Nat.zero_le _)
    omega
  have q7 : 4 * (s ^ 2) * C ^ 2 * (d ^ 3) ≤ 4 * (s ^ 2) * C ^ 2 * ((2 * s) ^ 3) :=
    mul_le_mul_of_nonneg_left (Nat.pow_le_pow_left hds 3) (Nat.zero_le _)
  have r3 : 4 * (s ^ 2) * C ^ 2 * ((2 * s) ^ 3) = 32 * C ^ 2 * (s ^ 5) := by ring
  omega

