-- Prove2me | solution 1 for FastFourierTransform.dft_conj_symm
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:27:39.921132+00:00
-- url     : https://prove2.me/submissions/a23523c7-f62c-4386-b2ac-a82de6375276

import Mathlib
import Definitions.Def_FastFourierTransform_dft

open FastFourierTransform

theorem solution (n : ℕ) (x : ℕ → ℂ) (hx : ∀ m, (x m).im = 0) (k : ℕ) (hk : k ≤ n) :
    dft n x (n - k) = (starRingEnd ℂ) (dft n x k) := by
  unfold dft
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_mul, ← Complex.exp_conj]
  have hxm : (starRingEnd ℂ) (x m) = x m := Complex.conj_eq_iff_im.mpr (hx m)
  rw [hxm]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : -(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((n - k : ℕ) : ℂ) / (n : ℂ))
      = (starRingEnd ℂ) (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k : ℂ) / (n : ℂ)))
        + ((-(m : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [map_neg, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast,
      map_ofNat]
    rw [Nat.cast_sub hk]
    push_cast; field_simp; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
