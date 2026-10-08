-- Prove2me | solution 1 for AvramDividend.Classical.positive_laplace_tail_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:16:47.968439+00:00
-- url     : https://prove2.me/submissions/1eb732a1-bdb3-4d17-b917-cf7024c8af42

import Mathlib
import Theorems.Thm_AvramDividend_Classical_discounted_positive_jump_tail_transform

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (μ : Measure ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-θ * t))
      ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}))) =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((1 - Real.exp (-θ * (z : ℝ))) / θ) ∂μ := by
  let tail : ℝ → ℝ≥0∞ :=
    fun t => μ {z : ℝ≥0 | t < (z : ℝ)}
  have htail : Antitone tail := by
    intro x y hxy
    apply measure_mono
    intro z hz
    exact lt_of_le_of_lt hxy hz
  have htail_meas :
      AEMeasurable tail (volume.restrict (Ioi (0 : ℝ))) :=
    htail.measurable.aemeasurable.restrict
  have hweight_meas :
      AEMeasurable
        (fun t : ℝ => ENNReal.ofReal (Real.exp (-θ * t)))
        (volume.restrict (Ioi (0 : ℝ))) := by
    exact (by fun_prop :
      Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-θ * t)))).aemeasurable.restrict
  change
    (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-θ * t))
      ∂((volume.restrict (Ioi (0 : ℝ))).withDensity tail)) = _
  rw [lintegral_withDensity_eq_lintegral_mul₀ htail_meas hweight_meas]
  simpa [tail] using discounted_positive_jump_tail_transform μ θ hθ
