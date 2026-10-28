-- Prove2me | solution 1 for AvramDividend.Classical.compensated_exp_quadratic_ratio_tendsto_zero_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:17:40.267719+00:00
-- url     : https://prove2.me/submissions/388d2330-5848-4f5e-89cb-b51352a132ab

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_neg_remainder_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory Filter
open AvramDividend.Classical

theorem solution
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hSq : Integrable (fun y : ℝ => y ^ 2) ν)
    (hInt : ∀ n : ℕ, Integrable (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2)) ν) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2) ∂ν)
      atTop (nhds 0) := by
  suffices h : Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2) ∂ν)
      atTop (nhds (∫ _y : ℝ, (0 : ℝ) ∂ν)) by
    simpa only [integral_zero] using h
  apply tendsto_integral_of_dominated_convergence (fun y : ℝ => y ^ 2)
    (fun n => (hInt n).aestronglyMeasurable) hSq
  · intro n
    filter_upwards [hneg] with y hy
    have hd : 0 < (n : ℝ) + 1 := by positivity
    have hz : ((n : ℝ) + 1) * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hd.le hy.le
    have hr := exp_neg_remainder_bounds (((n : ℝ) + 1) * y) hz
    have hd2 : 0 < ((n : ℝ) + 1) ^ 2 := sq_pos_of_pos hd
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.1 hd2.le)]
    apply (div_le_iff₀ hd2).2
    nlinarith [hr.2]
  · filter_upwards [hneg] with y hy
    have hle (n : ℕ) :
        0 ≤ (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2) ∧
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2) ≤
          (-y) / ((n : ℝ) + 1) := by
      have hd : 0 < (n : ℝ) + 1 := by positivity
      have hd2 : 0 < ((n : ℝ) + 1) ^ 2 := sq_pos_of_pos hd
      have hz : ((n : ℝ) + 1) * y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hd.le hy.le
      have hr := exp_neg_remainder_bounds (((n : ℝ) + 1) * y) hz
      constructor
      · exact div_nonneg hr.1 hd2.le
      · apply (div_le_iff₀ hd2).2
        have he : Real.exp (((n : ℝ) + 1) * y) ≤ 1 :=
          Real.exp_le_one_iff.mpr hz
        have hid :
            ((-y) / ((n : ℝ) + 1)) * (((n : ℝ) + 1) ^ 2) =
              -(((n : ℝ) + 1) * y) := by
          field_simp [ne_of_gt hd] <;> ring
        rw [hid]
        linarith [he]
    apply squeeze_zero' (g := fun n : ℕ => (-y) / ((n : ℝ) + 1))
    · exact Eventually.of_forall (fun n => (hle n).1)
    · exact Eventually.of_forall (fun n => (hle n).2)
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (-y)
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using h
