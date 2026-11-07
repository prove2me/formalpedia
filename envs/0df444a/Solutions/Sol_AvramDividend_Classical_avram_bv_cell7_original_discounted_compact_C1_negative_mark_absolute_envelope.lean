-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_discounted_compact_C1_negative_mark_absolute_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:56:23.769446+00:00
-- url     : https://prove2.me/submissions/68cd51c6-a661-4c6c-bf53-24c44dd871c4

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compact_C1_all_negative_mark_linear_magnitude_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal
noncomputable section

/-- The actual nonnegative-time C1 negative-jump difference retains the
    original BV linear-mark envelope after nonnegative discounting. -/
theorem solution
    (w : ℝ → ℝ) (a b L R : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0)
    (y z : ℝ) (hy : y ∈ Icc a b) (hz : z < 0) :
    |Real.exp (-(q * (t : ℝ))) * (w (y + z) - w y)| ≤
      (L + 4 * R / a) * (-z) := by
  have hMark :=
    AvramDividend.Classical.avram_bv_cell7_original_compact_C1_all_negative_mark_linear_magnitude_envelope
      w a b L R ha hab hL hR hLip hWbound y z hy hz
  have hqprod : 0 ≤ q * (t : ℝ) :=
    mul_nonneg hq (NNReal.coe_nonneg t)
  have hExpLE : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (neg_nonpos.mpr hqprod))
  have hExpNonneg : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hznonneg : 0 ≤ -z := by linarith
  have hCoeff : 0 ≤ L + 4 * R / a :=
    add_nonneg hL (div_nonneg (by nlinarith [hR]) (le_of_lt ha))
  calc
    |Real.exp (-(q * (t : ℝ))) * (w (y + z) - w y)| =
        Real.exp (-(q * (t : ℝ))) * |w (y + z) - w y| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-(q * (t : ℝ))) * ((L + 4 * R / a) * (-z)) :=
          mul_le_mul_of_nonneg_left hMark hExpNonneg
    _ ≤ 1 * ((L + 4 * R / a) * (-z)) :=
          mul_le_mul_of_nonneg_right hExpLE (mul_nonneg hCoeff hznonneg)
    _ = (L + 4 * R / a) * (-z) := one_mul _
