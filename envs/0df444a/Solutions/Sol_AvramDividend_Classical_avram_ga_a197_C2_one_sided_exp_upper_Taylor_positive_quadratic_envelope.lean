-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a197_C2_one_sided_exp_upper_Taylor_positive_quadratic_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:19:00.108655+00:00
-- url     : https://prove2.me/submissions/81adc61a-5c39-4f11-ae56-64f6078c5da7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- The positive second-order Taylor remainder of a C2 source with compact
jets inherits a one-sided exponential endpoint envelope. -/
theorem solution
    (w : ℝ → ℝ) (y r θ K M : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hw : |w y| ≤ M)
    (hderiv : |deriv w y| ≤ M)
    (hsecond : |iteratedDeriv 2 w y| ≤ M)
    (hupper : w (y + r) ≤ K * Real.exp (θ * (y + r))) :
    max (w (y + r) - w y - deriv w y * r -
        iteratedDeriv 2 w y / 2 * r^2) 0 ≤
      K * Real.exp (θ * (y + r)) +
        M * (1 + |r| + r^2 / 2) := by
  have hval : -w y ≤ M := (neg_le_abs _).trans hw
  have hprime : -(deriv w y * r) ≤ M * |r| := by
    calc
      -(deriv w y * r) ≤ |deriv w y * r| := neg_le_abs _
      _ = |deriv w y| * |r| := abs_mul _ _
      _ ≤ M * |r| :=
        mul_le_mul_of_nonneg_right hderiv (abs_nonneg _)
  have hjet : -(iteratedDeriv 2 w y / 2 * r^2) ≤ M / 2 * r^2 := by
    have hminus : -iteratedDeriv 2 w y ≤ M :=
      (neg_le_abs _).trans hsecond
    have hmul := mul_le_mul_of_nonneg_right hminus (sq_nonneg r)
    nlinarith
  have hRpos :
      0 ≤ K * Real.exp (θ * (y + r)) +
          M * (1 + |r| + r^2 / 2) := by
    have hF : 0 ≤ (1 : ℝ) + |r| + r^2 / 2 := by positivity
    exact add_nonneg (mul_nonneg hK (le_of_lt (Real.exp_pos _)))
      (mul_nonneg hM hF)
  apply max_le
  · nlinarith [hval,hprime,hjet,hupper]
  · exact hRpos
