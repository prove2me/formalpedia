-- Prove2me | solution 1 for FastFourierTransform.fft_eq_dft
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:30:58.241589+00:00
-- url     : https://prove2.me/submissions/ec333057-6391-496b-ac4f-9bba7d7af117

import Mathlib
import Definitions.Def_FastFourierTransform_dft
import Definitions.Def_FastFourierTransform_fft

open FastFourierTransform

namespace Ag3Aux_FftEqDft

theorem per (n : ℕ) (x : ℕ → ℂ) (k : ℕ) :
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

theorem sum_range_two_mul (N : ℕ) (f : ℕ → ℂ) :
    ∑ m ∈ Finset.range (2 * N), f m = ∑ m ∈ Finset.range N, (f (2 * m) + f (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

theorem evenodd (N : ℕ) (hN : 0 < N) (x : ℕ → ℂ) (k : ℕ) :
    dft (2 * N) x k =
      dft N (fun m => x (2 * m)) k
        + Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / ((2 * N : ℕ) : ℂ)))
            * dft N (fun m => x (2 * m + 1)) k := by
  unfold dft
  rw [sum_range_two_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  congr 1
  · congr 2
    push_cast; field_simp
  · rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; field_simp; ring

theorem dft_mod (n : ℕ) (x : ℕ → ℂ) (k : ℕ) : dft n x (k % n) = dft n x k := by
  conv_rhs => rw [← Nat.mod_add_div k n]
  generalize k / n = q
  induction q with
  | zero => simp
  | succ q ih => rw [mul_add, mul_one, ← add_assoc, per, ih]

end Ag3Aux_FftEqDft

open Ag3Aux_FftEqDft

theorem solution (p : ℕ) (x : ℕ → ℂ) (k : ℕ) :
    fft p x k = dft (2 ^ p) x k := by
  induction p generalizing x k with
  | zero =>
    simp [fft, dft]
  | succ p ih =>
    rw [fft, ih, ih, dft_mod, dft_mod, show 2 ^ (p + 1) = 2 * 2 ^ p by ring,
      evenodd _ (pow_pos two_pos p)]
    congr 3
    push_cast; ring
