-- Prove2me | solution 1 for FastFourierTransform.dft_periodic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:26:22.633975+00:00
-- url     : https://prove2.me/submissions/f2c3fcd5-62bb-4d78-8449-f986aba46a5c

import Mathlib
import Definitions.Def_FastFourierTransform_dft

open FastFourierTransform

theorem solution (n : ℕ) (x : ℕ → ℂ) (k : ℕ) :
    dft n x (k + n) = dft n x k := by
  unfold dft
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine Finset.sum_congr rfl (fun m _ => ?_)
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : -(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((k + n : ℕ) : ℂ) / (n : ℂ))
      = -(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k : ℂ) / (n : ℂ))
        + ((-(m : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; field_simp; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
