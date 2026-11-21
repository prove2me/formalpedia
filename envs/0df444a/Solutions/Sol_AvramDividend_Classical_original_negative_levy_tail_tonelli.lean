-- Prove2me | solution 1 for AvramDividend.Classical.original_negative_levy_tail_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:52:54.99895+00:00
-- url     : https://prove2.me/submissions/743bf434-8118-4ec4-9214-ff7dd9b13173

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ) (hν : ν (Ici (0 : ℝ)) = 0)
    (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ y : ℝ,
       ENNReal.ofReal
         (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ∂ν) =
      ∫⁻ t in Ioi (0 : ℝ),
        ν (Iio (-t)) * ENNReal.ofReal (1 - Real.exp (-θ * t)) := by
  have hf : 0 ≤ᵐ[ν] (fun y : ℝ => -y) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hν] with y hy
    have hy' : ¬ (0 : ℝ) ≤ y := by simpa only [mem_Ici] using hy
    exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hy'))
  have hm : AEMeasurable (fun y : ℝ => -y) ν :=
    (by fun_prop : Measurable (fun y : ℝ => -y)).aemeasurable
  have hi : ∀ t > 0,
      IntervalIntegrable (fun u : ℝ => 1 - Real.exp (-θ * u)) volume 0 t := by
    intro t ht
    have hc : Continuous (fun u : ℝ => 1 - Real.exp (-θ * u)) := by fun_prop
    exact hc.intervalIntegrable 0 t
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ 1 - Real.exp (-θ * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply sub_nonneg.mpr
    rw [← Real.exp_zero]
    rw [neg_mul]
    exact Real.exp_le_exp.mpr
      (neg_nonpos.mpr (mul_nonneg hθ.le (le_of_lt ht)))
  have ht (t : ℝ) : {y : ℝ | t < -y} = Iio (-t) := by
    ext y
    simp only [mem_setOf_eq, mem_Iio]
    constructor <;> intro h <;> linarith
  simpa only [ht] using
    (MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul ν
      (f := fun y : ℝ => -y)
      (g := fun t : ℝ => 1 - Real.exp (-θ * t)) hf hm hi hn)
