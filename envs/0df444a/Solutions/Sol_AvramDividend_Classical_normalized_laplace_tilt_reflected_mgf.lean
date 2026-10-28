-- Prove2me | solution 1 for AvramDividend.Classical.normalized_laplace_tilt_reflected_mgf
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:37:13.074479+00:00
-- url     : https://prove2.me/submissions/f9d5d598-734b-4409-904f-2f4def73886a

import Mathlib

open MeasureTheory
open scoped ENNReal

theorem solution
    {μ : Measure ℝ} (s₀ C t : ℝ)
    (hCpos : 0 < C) (ht : 0 < t)
    (hInt : Integrable (fun x : ℝ => Real.exp (-((s₀ + t) * x))) μ) :
    let μ₀ := μ.withDensity
      (fun x => ENNReal.ofReal (C⁻¹ * Real.exp (-(s₀ * x))))
    Integrable (fun y : ℝ => Real.exp (t * y)) (Measure.map (fun x : ℝ => -x) μ₀) ∧
      (∫ y, Real.exp (t * y) ∂(Measure.map (fun x : ℝ => -x) μ₀)) =
        C⁻¹ * ∫ x, Real.exp (-((s₀ + t) * x)) ∂μ := by
  intro μ₀
  have hd : Measurable (fun x : ℝ => ENNReal.ofReal (C⁻¹ * Real.exp (-(s₀ * x)))) := by
    fun_prop
  have hfg : ∀ x : ℝ, (ENNReal.ofReal (C⁻¹ * Real.exp (-(s₀ * x)))).toReal * Real.exp (t * -x)
      = C⁻¹ * Real.exp (-((s₀ + t) * x)) := by
    intro x
    rw [ENNReal.toReal_ofReal (by positivity), mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hmeas : AEMeasurable (fun x : ℝ => -x) μ₀ := measurable_neg.aemeasurable
  have hsm : AEStronglyMeasurable (fun y : ℝ => Real.exp (t * y)) (Measure.map (fun x : ℝ => -x) μ₀) :=
    (by fun_prop : Continuous fun y : ℝ => Real.exp (t * y)).aestronglyMeasurable
  have hlt : ∀ᵐ x ∂μ, ENNReal.ofReal (C⁻¹ * Real.exp (-(s₀ * x))) < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  constructor
  · rw [integrable_map_measure hsm hmeas]
    show Integrable ((fun y : ℝ => Real.exp (t * y)) ∘ fun x => -x) μ₀
    rw [integrable_withDensity_iff_integrable_smul' hd hlt]
    simp only [Function.comp, smul_eq_mul, hfg]
    exact hInt.const_mul _
  · rw [integral_map hmeas hsm, integral_withDensity_eq_integral_toReal_smul hd hlt]
    simp only [smul_eq_mul, hfg]
    exact integral_const_mul _ _
