-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_discounted_single_contact_Taylor_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:32:22.030189+00:00
-- url     : https://prove2.me/submissions/87e65ffa-e0ee-4bdb-93dd-0c31c2507178

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A single discounted C1 Taylor contact remainder is bounded by the
increment whenever its endpoint value difference and initial derivative
have a common Lipschitz envelope. -/
theorem solution
    (w : ℝ → ℝ) (q u z c L : ℝ)
    (hq : 0 ≤ q) (hu : 0 ≤ u) (hL : 0 ≤ L)
    (hLip : |w (z + c) - w z| ≤ L * |c|)
    (hDeriv : |deriv w z| ≤ L) :
    |Real.exp (-(q * u)) *
        (w (z + c) - w z - deriv w z * c)| ≤
      (2 * L) * |c| := by
  have he0 : 0 ≤ Real.exp (-(q * u)) :=
    le_of_lt (Real.exp_pos _)
  have he1 : Real.exp (-(q * u)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hq hu)
  have hd : |deriv w z * c| ≤ L * |c| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hDeriv (abs_nonneg c)
  have ht : |w (z + c) - w z - deriv w z * c| ≤
      (2 * L) * |c| := by
    calc
      _ ≤ |w (z + c) - w z| + |deriv w z * c| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (w (z + c) - w z) 0 (deriv w z * c))
      _ ≤ L * |c| + L * |c| := add_le_add hLip hd
      _ = (2 * L) * |c| := by ring
  calc
    _ = Real.exp (-(q * u)) *
        |w (z + c) - w z - deriv w z * c| := by
          rw [abs_mul, abs_of_nonneg he0]
    _ ≤ Real.exp (-(q * u)) * ((2 * L) * |c|) :=
      mul_le_mul_of_nonneg_left ht he0
    _ ≤ 1 * ((2 * L) * |c|) :=
      mul_le_mul_of_nonneg_right he1 (by positivity)
    _ = (2 * L) * |c| := by ring
