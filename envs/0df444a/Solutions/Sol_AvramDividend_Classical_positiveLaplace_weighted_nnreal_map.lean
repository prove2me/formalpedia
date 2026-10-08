-- Prove2me | solution 1 for AvramDividend.Classical.positiveLaplace_weighted_nnreal_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:09:09.970704+00:00
-- url     : https://prove2.me/submissions/757401dc-25d8-4d78-8aad-ac9690dd501c

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ≥0) (a s : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x))
      ∂Measure.map (fun z : ℝ≥0 => (z : ℝ))
        (μ.withDensity
          (fun z : ℝ≥0 =>
            ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))))) =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal (Real.exp (-s * (z : ℝ))) *
          ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ))) ∂μ := by
  let w : ℝ≥0 → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))
  let f : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-s * x))
  have hw : AEMeasurable w μ := by
    apply Measurable.aemeasurable
    dsimp [w]
    fun_prop
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hcoe : Measurable (fun z : ℝ≥0 => (z : ℝ)) := by
    fun_prop
  change
    (∫⁻ x : ℝ, f x
      ∂Measure.map (fun z : ℝ≥0 => (z : ℝ)) (μ.withDensity w)) =
      ∫⁻ z : ℝ≥0, f (z : ℝ) * w z ∂μ
  rw [lintegral_map hf hcoe]
  simpa [Function.comp_apply, mul_comm] using
    (lintegral_withDensity_eq_lintegral_mul₀ hw
      ((hf.comp hcoe).aemeasurable))
