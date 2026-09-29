-- Prove2me | solution 1 for FastFourierTransform.dft_even_odd_split
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:29:06.562056+00:00
-- url     : https://prove2.me/submissions/04918e64-e9be-4b96-aa47-a134bf47d438

import Mathlib
import Definitions.Def_FastFourierTransform_dft

open FastFourierTransform

namespace Ag3Aux_DftEvenOdd

theorem sum_range_two_mul (N : ℕ) (f : ℕ → ℂ) :
    ∑ m ∈ Finset.range (2 * N), f m = ∑ m ∈ Finset.range N, (f (2 * m) + f (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

end Ag3Aux_DftEvenOdd

open Ag3Aux_DftEvenOdd

theorem solution (N : ℕ) (hN : 0 < N) (x : ℕ → ℂ) (k : ℕ) :
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
