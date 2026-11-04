-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_exact_discount_nnreal_width_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:22:16.525831+00:00
-- url     : https://prove2.me/submissions/a4c46bec-087e-4848-bae0-8f551ba14542

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original ENNReal discount oscillation is bounded by q times cell width. -/
theorem solution (q a b : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) :
    ENNReal.ofReal (Real.exp (-(q * a))) ≤
      ENNReal.ofReal (Real.exp (-(q * b))) +
        ENNReal.ofReal (q * (b - a)) := by
  have hwidth : 0 ≤ q * (b - a) :=
    mul_nonneg hq (sub_nonneg.mpr hab)
  calc
    ENNReal.ofReal (Real.exp (-(q * a))) ≤
        ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) :=
      ENNReal.ofReal_le_ofReal
        (avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz
          q a b hq ha hab)
    _ = ENNReal.ofReal (Real.exp (-(q * b))) +
          ENNReal.ofReal (q * (b - a)) :=
      ENNReal.ofReal_add (le_of_lt (Real.exp_pos _)) hwidth
