-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_real_interval_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:30:12.312545+00:00
-- url     : https://prove2.me/submissions/a8bfc087-dd0d-4b1e-96a2-4ec448e755a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every true original BV source intrinsic negative-mark measure
increment is a nonnegative real and is dominated by physical drift
less the actual source increment on one common almost-sure event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      let J : ℝ :=
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal
      0 ≤ J ∧
        J ≤ ((t : ℝ) - (s : ℝ)) * X.drift -
          (X.X t ω - X.X s ω) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hω
  intro s t hst
  dsimp only
  have hmass :
      (∫⁻ p,
        (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u)))).toReal =
      (∑' (v : ℝ≥0),
        if s < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal :=
    congrArg ENNReal.toReal
      (avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
        X ω s t)
  have hinc := hinterval s t hst
  rw [← hmass] at hinc
  have hmono : 0 ≤ R t - R s := sub_nonneg.mpr (hRmono hst)
  constructor
  · apply ENNReal.toReal_nonneg
  · linarith only [hinc, hmono]
