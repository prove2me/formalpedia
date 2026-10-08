-- Prove2me | solution 1 for AvramDividend.Classical.positiveLaplace_tilted_kernel_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:52:24.657853+00:00
-- url     : https://prove2.me/submissions/5a18b070-c174-4db4-a9f6-a238f83e81cc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positive_laplace_tail_withDensity
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_weighted_cumulative_nnreal
import Theorems.Thm_AvramDividend_Classical_positive_tilted_kernel_pointwise_identity

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (μ : Measure ℝ≥0) [SFinite μ]
    (a s : ℝ) (ha : 0 ≤ a) (hs : 0 < s) :
    let tailMeasure : Measure ℝ :=
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)})
    let weightedMeasure : Measure ℝ :=
      Measure.map (fun z : ℝ≥0 => (z : ℝ))
        (μ.withDensity
          (fun z : ℝ≥0 =>
            ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))))
    let cumulativeMeasure : Measure ℝ :=
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => weightedMeasure (Iic x))
    let κ : Measure ℝ := tailMeasure + cumulativeMeasure
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal
          ((1 - Real.exp (-(s + a) * (z : ℝ))) / s) ∂μ := by
  let β : Measure ℝ :=
    Measure.map (fun z : ℝ≥0 => (z : ℝ))
      (μ.withDensity
        (fun z : ℝ≥0 =>
          ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))))
  have hβmono : Monotone (fun x : ℝ => β (Iic x)) := by
    intro x y hxy
    exact measure_mono (Iic_subset_Iic.mpr hxy)
  have hβmeas :
      AEMeasurable (fun x : ℝ => β (Iic x))
        (volume.restrict (Ioi (0 : ℝ))) :=
    hβmono.measurable.aemeasurable.restrict
  have hexp :
      AEMeasurable
        (fun x : ℝ => ENNReal.ofReal (Real.exp (-s * x)))
        (volume.restrict (Ioi (0 : ℝ))) := by
    exact (by fun_prop :
      Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-s * x)))).aemeasurable.restrict
  have hcum :
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x))
        ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
          (fun x : ℝ => β (Iic x)))) =
        ENNReal.ofReal (1 / s) *
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-s * (z : ℝ))) *
              ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ))) ∂μ) := by
    rw [lintegral_withDensity_eq_lintegral_mul₀ hβmeas hexp]
    simpa [β, mul_comm] using
      (positiveLaplace_weighted_cumulative_nnreal μ a s hs)
  have htailMeas : Measurable (fun z : ℝ≥0 =>
      ENNReal.ofReal ((1 - Real.exp (-s * (z : ℝ))) / s)) := by
    fun_prop
  dsimp
  change
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x))
      ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
          (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}) +
        (volume.restrict (Ioi (0 : ℝ))).withDensity
          (fun x : ℝ => β (Iic x)))) = _
  rw [lintegral_add_measure]
  rw [positive_laplace_tail_withDensity μ s hs]
  rw [hcum]
  rw [← lintegral_const_mul'
    (μ := μ)
    (ENNReal.ofReal (1 / s))
    (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-s * (z : ℝ))) *
        ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ))))
    ENNReal.ofReal_ne_top]
  rw [← lintegral_add_left htailMeas]
  apply lintegral_congr
  intro z
  exact positive_tilted_kernel_pointwise_identity a s (z : ℝ) ha hs z.2
