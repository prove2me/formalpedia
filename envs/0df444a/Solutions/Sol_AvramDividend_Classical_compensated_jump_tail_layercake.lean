-- Prove2me | solution 1 for AvramDividend.Classical.compensated_jump_tail_layercake
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:52:33.181275+00:00
-- url     : https://prove2.me/submissions/df9e4969-4828-4618-a31c-997a50d7388c

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (μ : Measure ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ z : ℝ≥0,
       ENNReal.ofReal
         (∫ t in (0 : ℝ)..(z : ℝ), (1 - Real.exp (-θ * t))) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ),
        μ {z : ℝ≥0 | t < (z : ℝ)} *
          ENNReal.ofReal (1 - Real.exp (-θ * t)) := by
  have hf : 0 ≤ᵐ[μ] (fun z : ℝ≥0 => (z : ℝ)) :=
    Filter.Eventually.of_forall (fun z => by positivity)
  have hm : AEMeasurable (fun z : ℝ≥0 => (z : ℝ)) μ :=
    (by fun_prop : Measurable (fun z : ℝ≥0 => (z : ℝ))).aemeasurable
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
  simpa using
    (MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul μ
      (f := fun z : ℝ≥0 => (z : ℝ))
      (g := fun t : ℝ => 1 - Real.exp (-θ * t)) hf hm hi hn)
