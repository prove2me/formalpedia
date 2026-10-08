-- Prove2me | solution 1 for AvramDividend.Classical.exp_negative_compensated_secant_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T18:00:55.295303+00:00
-- url     : https://prove2.me/submissions/78c28b4e-403c-4977-8156-705223571d9e

import Mathlib

theorem solution (y : ℝ) (hy : y < 0) :
    Filter.Tendsto
      (fun n : ℕ => (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1))
      Filter.atTop (nhds (-y)) := by
  have hrecip :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hnum (n : ℕ) :
      0 ≤ (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1) ∧
        (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1) ≤
          (1 : ℝ) / ((n : ℝ) + 1) := by
    have hθ : 0 < ((n : ℝ) + 1) := by positivity
    have hz : ((n : ℝ) + 1) * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ.le hy.le
    have hle : Real.exp (((n : ℝ) + 1) * y) ≤ 1 :=
      Real.exp_le_one_iff.mpr hz
    have hpos : 0 ≤ Real.exp (((n : ℝ) + 1) * y) :=
      (Real.exp_pos _).le
    constructor
    · exact div_nonneg (by linarith) hθ.le
    · exact div_le_div_of_nonneg_right (by linarith) hθ.le
  have hsqueeze :
      Filter.Tendsto
        (fun n : ℕ => (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1))
        Filter.atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero (fun n => (hnum n).1) (fun n => (hnum n).2)
    exact hrecip
  have hquot :
      Filter.Tendsto
        (fun n : ℕ => (Real.exp (((n : ℝ) + 1) * y) - 1) / ((n : ℝ) + 1))
        Filter.atTop (nhds (0 : ℝ)) := by
    have hn : (fun n : ℕ =>
        (Real.exp (((n : ℝ) + 1) * y) - 1) / ((n : ℝ) + 1)) =
      (fun n : ℕ =>
        -((1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1))) := by
      funext n
      ring
    rw [hn]
    simpa using hsqueeze.neg
  have hrewrite : (fun n : ℕ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) =
      (fun n : ℕ =>
        (Real.exp (((n : ℝ) + 1) * y) - 1) / ((n : ℝ) + 1) - y) := by
    funext n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hrewrite]
  simpa using hquot.sub (tendsto_const_nhds (x := y))
