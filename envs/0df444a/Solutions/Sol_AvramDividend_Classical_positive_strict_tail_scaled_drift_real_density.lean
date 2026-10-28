-- Prove2me | solution 1 for AvramDividend.Classical.positive_strict_tail_scaled_drift_real_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:28:45.36261+00:00
-- url     : https://prove2.me/submissions/63f9b889-a016-49bd-a5c4-1be12cec3abe

import Theorems.Thm_AvramDividend_Classical_positive_strict_tail_measure_real_density
import Theorems.Thm_AvramDividend_Classical_real_nonnegative_scalar_withDensity_unrestricted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Drift-normalised strict-tail kernel has the exact truncated real density. -/
theorem solution (μ : Measure ℝ≥0)
    (hmoment : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤)
    (d : ℝ) (hd : 0 < d) :
    (ENNReal.ofReal d)⁻¹ •
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}) =
    (volume : Measure ℝ).withDensity
      (fun t : ℝ => ENNReal.ofReal
        (if 0 < t then (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal / d else 0)) := by
  let K : ℝ → ℝ := fun t =>
    if 0 < t then (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal else 0
  have hcoeff : (ENNReal.ofReal d)⁻¹ = ENNReal.ofReal (d⁻¹) :=
    (ENNReal.ofReal_inv_of_pos hd).symm
  have hpositive : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  calc
    _ = ENNReal.ofReal (d⁻¹) •
          (volume : Measure ℝ).withDensity
            (fun t : ℝ => ENNReal.ofReal (K t)) := by
      rw [hcoeff]
      exact congrArg (fun m : Measure ℝ => ENNReal.ofReal (d⁻¹) • m)
        (positive_strict_tail_measure_real_density μ hmoment)
    _ = (volume : Measure ℝ).withDensity
          (fun t : ℝ => ENNReal.ofReal (d⁻¹ * K t)) :=
        real_nonnegative_scalar_withDensity_unrestricted (d⁻¹) hpositive K
    _ = (volume : Measure ℝ).withDensity
          (fun t : ℝ => ENNReal.ofReal
            (if 0 < t then (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal / d else 0)) := by
      congr 1
      funext t
      by_cases ht : 0 < t
      · simp only [K, if_pos ht, div_eq_mul_inv, mul_comm]
      · simp [K, ht]