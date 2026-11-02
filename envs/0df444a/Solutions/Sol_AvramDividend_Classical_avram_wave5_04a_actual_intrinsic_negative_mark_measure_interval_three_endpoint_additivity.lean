-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_negative_mark_measure_interval_three_endpoint_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:49:36.379656+00:00
-- url     : https://prove2.me/submissions/ad5ca435-6efe-4f0f-9ebb-32c9032567d5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The true intrinsic source negative-mark integral is finitely
additive on consecutive original time intervals, pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t r : ℝ≥0) (hst : s ≤ t) (htr : t ≤ r) :
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ r then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) +
    (∫⁻ p,
      (if t < p.1 ∧ p.1 ≤ r then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  rw [avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
      X ω s r,
    avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
      X ω s t,
    avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
      X ω t r]
  exact avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity
    X ω s t r hst htr
