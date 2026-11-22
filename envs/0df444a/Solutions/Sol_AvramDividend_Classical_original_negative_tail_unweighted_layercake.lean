-- Prove2me | solution 1 for AvramDividend.Classical.original_negative_tail_unweighted_layercake
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:16:44.175056+00:00
-- url     : https://prove2.me/submissions/cdfb0b2f-67f5-4539-a31e-a03bba809713

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0) :
    (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂ν) =
      ∫⁻ t in Ioi (0 : ℝ), ν (Iio (-t)) := by
  have hf : 0 ≤ᵐ[ν] (fun y : ℝ => -y) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hSupp] with y hy
    have hy' : y < 0 := lt_of_not_ge (by simpa only [mem_Ici] using hy)
    exact neg_nonneg.mpr hy'.le
  have ht (t : ℝ) : {y : ℝ | t < -y} = Iio (-t) := by
    ext y
    simp only [mem_setOf_eq, mem_Iio]
    constructor <;> intro h <;> linarith
  simpa only [ht, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul, mul_one, ENNReal.ofReal_one, mul_one] using
    (MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul ν
      (f := fun y : ℝ => -y) (g := fun t : ℝ => (1 : ℝ))
      hf
      ((by fun_prop : Measurable (fun y : ℝ => -y)).aemeasurable)
      (by intro t ht; exact intervalIntegrable_const)
      (Filter.Eventually.of_forall (fun _ => by norm_num)))
