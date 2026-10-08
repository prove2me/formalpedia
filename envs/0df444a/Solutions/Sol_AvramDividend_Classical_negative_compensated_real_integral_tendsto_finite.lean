-- Prove2me | solution 1 for AvramDividend.Classical.negative_compensated_real_integral_tendsto_finite
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:42:13.252087+00:00
-- url     : https://prove2.me/submissions/eee3a887-c084-4cd0-8a33-0411c5913804

import Mathlib

open MeasureTheory Filter

theorem AvramDividend.Classical.negative_compensated_real_integral_tendsto_finite
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : Integrable (fun y : ℝ => |y|) ν)
    (hint : ∀ n : ℕ, Integrable (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ν) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂ν)
      atTop (nhds (∫ y : ℝ, |y| ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun y : ℝ => |y|)
    (fun n => (hint n).aestronglyMeasurable) hA
  · intro n
    filter_upwards [hneg] with y hy
    have ht : 0 < (n : ℝ) + 1 := by positivity
    have hz : ((n : ℝ) + 1) * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht.le hy.le
    have he := Real.exp_le_one_iff.mpr hz
    have hp : 0 ≤ Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y := by
      linarith [Real.add_one_le_exp (((n : ℝ) + 1) * y)]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hp ht.le),
      abs_of_neg hy, div_le_iff₀ ht]
    nlinarith
  · filter_upwards [hneg] with y hy
    have hzero : Tendsto (fun n : ℕ =>
        (Real.exp (((n : ℝ) + 1) * y) - 1) / ((n : ℝ) + 1))
        atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      apply squeeze_zero' (g := fun n : ℕ => 1 / ((n : ℝ) + 1))
      · exact Eventually.of_forall (fun n => by
          exact norm_nonneg _)
      · exact Eventually.of_forall (fun n => by
          have ht : 0 < (n : ℝ) + 1 := by positivity
          rw [Real.norm_eq_abs, abs_of_nonpos
            (div_nonpos_of_nonpos_of_nonneg
              (sub_nonpos.mpr (Real.exp_le_one_iff.mpr
                (mul_nonpos_of_nonneg_of_nonpos ht.le hy.le))) ht.le)]
          rw [← neg_div, div_le_div_iff_of_pos_right ht]
          linarith [Real.exp_pos (((n : ℝ) + 1) * y)])
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hs := hzero.sub (tendsto_const_nhds (x := y))
    convert hs using 1
    · ext n
      have ht : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      <;> ring
    · rw [abs_of_neg hy]
      ring


theorem solution
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : Integrable (fun y : ℝ => |y|) ν)
    (hint : ∀ n : ℕ, Integrable (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ν) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂ν)
      atTop (nhds (∫ y : ℝ, |y| ∂ν)) := AvramDividend.Classical.negative_compensated_real_integral_tendsto_finite ν hneg hA hint
#print axioms solution
