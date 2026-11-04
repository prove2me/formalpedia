-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:07:41.063579+00:00
-- url     : https://prove2.me/submissions/4c7ed103-8f1e-4e96-adf9-68ae3eaf0c5f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- Nonnegative-time discount has a global one-sided Lipschitz bound. -/
theorem solution (q a b : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-(q * a)) ≤ Real.exp (-(q * b)) + q * (b - a) := by
  let y : ℝ := q * (b - a)
  let e : ℝ := Real.exp (-(q * a))
  have hy : 0 ≤ y := mul_nonneg hq (sub_nonneg.mpr hab)
  have he0 : 0 ≤ e := le_of_lt (Real.exp_pos _)
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hq ha])
  have hbase : 1 - y ≤ Real.exp (-y) := Real.one_sub_le_exp_neg y
  have hmul : e * (1 - y) ≤ e * Real.exp (-y) :=
    mul_le_mul_of_nonneg_left hbase he0
  have hexp : e * Real.exp (-y) = Real.exp (-(q * b)) := by
    change Real.exp (-(q * a)) * Real.exp (-(q * (b - a))) = _
    rw [← Real.exp_add]
    congr 1
    ring
  have hrest : e * y ≤ y := by
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right he1 hy)
  change e ≤ Real.exp (-(q * b)) + y
  nlinarith
