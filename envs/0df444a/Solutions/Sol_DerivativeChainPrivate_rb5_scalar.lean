-- Prove2me | solution 1 for DerivativeChainPrivate.rb5_scalar
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:55:11.073396+00:00
-- url     : https://prove2.me/submissions/06dfcc7e-2149-47ae-b9c6-0898a8ca3f79

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (N c u V : ℝ) (hc : 0 ≤ c) (hNc : c < N)
    (hV : 0 ≤ V) (huV : u ^ 2 + V ≤ 1) :
    1 + Real.sqrt (u ^ 2 + c * V / N) + c * Real.sqrt (V / N) ≤
      1 + Real.sqrt (1 + c ^ 2 / (N - c)) := by
  have hN : 0 < N := lt_of_le_of_lt hc hNc
  have hd : 0 < N - c := sub_pos.mpr hNc
  have hA : 0 ≤ u ^ 2 + c * V / N := by positivity
  have hB : 0 ≤ V / N := by positivity
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have hsD := Real.sq_sqrt (show 0 ≤ N - c from le_of_lt hd)
  have hsInv : (c / Real.sqrt (N - c)) ^ 2 = c ^ 2 / (N - c) := by
    rw [div_pow, hsD]
  have hInner : (Real.sqrt (u ^ 2 + c * V / N) + c * Real.sqrt (V / N)) ^ 2 ≤
      (1 + c ^ 2 / (N - c)) * (u ^ 2 + V) := by
    have hSqrt : 0 < Real.sqrt (N - c) := Real.sqrt_pos.mpr hd
    have hDen : Real.sqrt (N - c) ≠ 0 := ne_of_gt hSqrt
    have hCross : Real.sqrt (N - c) * (c / Real.sqrt (N - c)) = c :=
      mul_div_cancel₀ c hDen
    have hEnergy : (u ^ 2 + c * V / N) + (N - c) * (V / N) = u ^ 2 + V := by
      field_simp
      ring
    have hCS (x y r s : ℝ) : (x * r + y * s) ^ 2 ≤
        (x ^ 2 + y ^ 2) * (r ^ 2 + s ^ 2) := by
      nlinarith only [sq_nonneg (x * s - y * r)]
    have h := hCS (Real.sqrt (u ^ 2 + c * V / N))
      (Real.sqrt (N - c) * Real.sqrt (V / N)) 1 (c / Real.sqrt (N - c))
    rw [mul_one, mul_assoc, mul_comm (Real.sqrt (V / N)), ← mul_assoc,
      hCross, mul_pow, hsD, hsB, hsA, hsInv, one_pow, hEnergy] at h
    simpa [mul_comm] using h
  have hFactor : 0 ≤ 1 + c ^ 2 / (N - c) := by positivity
  have hBound := hInner.trans (mul_le_mul_of_nonneg_left huV hFactor)
  have hFinal := Real.le_sqrt_of_sq_le (by simpa using hBound)
  linarith
