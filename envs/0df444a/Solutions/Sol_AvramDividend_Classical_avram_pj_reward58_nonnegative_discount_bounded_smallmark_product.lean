-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward58_nonnegative_discount_bounded_smallmark_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:51:05.749537+00:00
-- url     : https://prove2.me/submissions/e93d7377-6655-486b-ae25-2724fad17364

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0)
    (z g M : ℝ) (hsmall : |z| ≤ 1)
    (hM : 0 ≤ M) (hg : |g| ≤ M) :
    |Real.exp (-(q * (t : ℝ))) * (g * z)| ≤ M := by
  have ht : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
  have hExp : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hExp1 : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hq ht]
  rw [abs_mul, abs_mul, abs_of_nonneg hExp]
  calc
    Real.exp (-(q * (t : ℝ))) * (|g| * |z|) ≤ 1 * (M * 1) := by
      gcongr
    _ = M := by ring
