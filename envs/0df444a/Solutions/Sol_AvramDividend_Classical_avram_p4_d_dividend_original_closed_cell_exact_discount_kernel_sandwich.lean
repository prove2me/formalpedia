-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_closed_cell_exact_discount_kernel_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:38:38.273697+00:00
-- url     : https://prove2.me/submissions/6246b411-2dd2-499b-b1b3-96037a995aee

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

noncomputable section

/-- The original nonnegative-time discount is between its interval endpoint values. -/
theorem solution (q : ℝ) (hq : 0 ≤ q) (a t b : ℝ≥0)
    (hat : a ≤ t) (htb : t ≤ b) :
    ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) ≤
      ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) ∧
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) := by
  have htbR : (t : ℝ) ≤ (b : ℝ) := by exact_mod_cast htb
  have hatR : (a : ℝ) ≤ (t : ℝ) := by exact_mod_cast hat
  constructor
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left htbR hq
    linarith
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hatR hq
    linarith
