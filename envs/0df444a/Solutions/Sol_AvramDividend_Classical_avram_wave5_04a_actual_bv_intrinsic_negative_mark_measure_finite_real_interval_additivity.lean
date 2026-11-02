-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:51:15.776788+00:00
-- url     : https://prove2.me/submissions/3b2c47ed-6fc1-4f17-a3a7-8b324a57c90a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_source_jump_measure_interval_integrable_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A genuine real-valued, finite, nonnegative additive increment
functional from original BV Levy left-jump negative-mark measure.
The a.s. event is uniform in all three ordered time endpoints. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ J : ℝ≥0 → ℝ≥0 → ℝ,
      (∀ (a b : ℝ≥0),
        J a b =
          (∫⁻ p,
            (if a < p.1 ∧ p.1 ≤ b then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal) ∧
      (∀ a b, 0 ≤ J a b) ∧
      ∀ (s t r : ℝ≥0), s ≤ t → t ≤ r →
        J s r = J s t + J t r := by
  filter_upwards
    [avram_wave5_04a_actual_bv_intrinsic_negative_source_jump_measure_interval_integrable_finite
      X hBV] with ω hfinite
  let J (a b : ℝ≥0) : ℝ :=
    (∫⁻ p,
      (if a < p.1 ∧ p.1 ≤ b then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))).toReal
  refine ⟨J, ?_, ?_, ?_⟩
  · intro a b
    rfl
  · intro a b
    apply ENNReal.toReal_nonneg
  · intro s t r hst htr
    change
      (∫⁻ p,
        (if s < p.1 ∧ p.1 ≤ r then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u)))).toReal =
      J s t + J t r
    have hmeasure :
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ r then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧
            X.X v ω - Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).map
            (fun v : ℝ≥0 => (v,
              X.X v ω - Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v)))) =
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧
            X.X v ω - Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).map
            (fun v : ℝ≥0 => (v,
              X.X v ω - Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v)))) +
        (∫⁻ p,
          (if t < p.1 ∧ p.1 ≤ r then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧
            X.X v ω - Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).map
            (fun v : ℝ≥0 => (v,
              X.X v ω - Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v)))) := by
      rw [avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum X ω s r,
        avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum X ω s t,
        avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum X ω t r]
      exact avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity
        X ω s t r hst htr
    rw [hmeasure]
    exact ENNReal.toReal_add (hfinite s t hst) (hfinite t r htr)
