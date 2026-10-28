-- Prove2me | solution 1 for D1Bound5.all_large_retained_gap_monomial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:54:39.50219+00:00
-- url     : https://prove2.me/submissions/9c7c904f-9748-4a4c-9ae2-c15e0b923a8e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

section
namespace D1Bound5





/-- Exact coefficient check in the retained-gap specialization. This is the
number that allows the no-small-entry argument to use G=400. -/
theorem all_large_retained_gap_constant :
    (400 : ℝ) <
      3 ^ 5 * ((9999 / 10000) * (200 / 19) ^ 2) *
        (1 / 8 - (51051 / 400000) / 81) ^ 2 := by
  norm_num

/-- The retained H48 coefficient yields the exact monomial growth used
throughout the no-small-entry overlap table. Its hypotheses are the retained
gap estimate itself and the elementary bounds on its normalized Vandermonde
parameter; the analytic retained estimate is a separate theorem. -/
theorem _root_.solution
    (A B S C Q : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B) (hS : 0 < S)
    (hQ : 0 < Q) (hQ8 : Q ≤ 8)
    (hgap :
      3 ^ 5 * ((9999 / 10000) * (200 / 19) ^ 2) *
          (1 / Q - (51051 / 400000) / (A ^ 2 * B ^ 2)) ^ 2 *
          (A ^ 7 * B ^ 5 * S ^ 3) < C) :
    400 * (A ^ 7 * B ^ 5 * S ^ 3) < C := by
  have hAB : (81 : ℝ) ≤ A ^ 2 * B ^ 2 := by
    calc
      (81 : ℝ) = 3 ^ 2 * 3 ^ 2 := by norm_num
      _ ≤ A ^ 2 * B ^ 2 := by
        gcongr <;> first | assumption | norm_num
  have hABpos : 0 < A ^ 2 * B ^ 2 := lt_of_lt_of_le (by norm_num) hAB
  have hinv : (1 / 8 : ℝ) ≤ 1 / Q := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) hQ).2
    simpa using hQ8
  have herr : (51051 / 400000 : ℝ) / (A ^ 2 * B ^ 2) ≤
      (51051 / 400000) / 81 := by
    apply (div_le_div_iff₀ hABpos (by norm_num : (0 : ℝ) < 81)).2
    nlinarith only [hAB]
  have hbase : (0 : ℝ) < 1 / 8 - (51051 / 400000) / 81 := by norm_num
  have hdelta : (1 / 8 : ℝ) - (51051 / 400000) / 81 ≤
      1 / Q - (51051 / 400000) / (A ^ 2 * B ^ 2) := by
    linarith only [hinv, herr]
  have hsquare : ((1 / 8 : ℝ) - (51051 / 400000) / 81) ^ 2 ≤
      (1 / Q - (51051 / 400000) / (A ^ 2 * B ^ 2)) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hdelta)
      (add_nonneg (hbase.le.trans hdelta) hbase.le)
    nlinarith only [hp]
  have hcoefficient : (400 : ℝ) <
      3 ^ 5 * ((9999 / 10000) * (200 / 19) ^ 2) *
        (1 / Q - (51051 / 400000) / (A ^ 2 * B ^ 2)) ^ 2 := by
    exact all_large_retained_gap_constant.trans_le
      (mul_le_mul_of_nonneg_left hsquare (by norm_num))
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hmonomial : 0 < A ^ 7 * B ^ 5 * S ^ 3 :=
    mul_pos (mul_pos (pow_pos hApos _) (pow_pos hBpos _)) (pow_pos hS _)
  exact (mul_lt_mul_of_pos_right hcoefficient hmonomial).trans hgap

end D1Bound5
end
