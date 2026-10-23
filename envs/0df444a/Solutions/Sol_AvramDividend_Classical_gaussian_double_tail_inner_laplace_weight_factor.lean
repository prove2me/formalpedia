-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_inner_laplace_weight_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T15:04:21.647315+00:00
-- url     : https://prove2.me/submissions/1fbfc5fe-dc60-424f-9cfd-8f3b36e1f284

import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_time_weight_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) (φ θ t : ℝ) :
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) =
      ENNReal.ofReal (Real.exp (-θ * t)) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ) := by
  have hset : MeasurableSet {z : ℝ | 0 < t ∧ t < z} := by
    by_cases ht : 0 < t
    · have heq : {z : ℝ | 0 < t ∧ t < z} = Ioi t := by
        ext z
        simp [ht]
      rw [heq]
      exact measurableSet_Ioi
    · have heq : {z : ℝ | 0 < t ∧ t < z} = ∅ := by
        ext z
        simp [ht]
      rw [heq]
      exact MeasurableSet.empty
  have hprod : Measurable
      (fun z : ℝ =>
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-φ * z))) := by
    fun_prop
  have hmeas : Measurable
      (fun z : ℝ =>
        if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-φ * z))
        else 0) :=
    Measurable.ite hset hprod measurable_const
  calc
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) =
       ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * t)) *
         (if 0 < t ∧ t < z then
           ENNReal.ofReal (z - t) *
             ENNReal.ofReal (Real.exp (-φ * z))
          else 0) ∂μ := by
      apply lintegral_congr
      intro z
      exact gaussian_double_tail_time_weight_factor φ θ t z
    _ = ENNReal.ofReal (Real.exp (-θ * t)) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ) := lintegral_const_mul _ hmeas
