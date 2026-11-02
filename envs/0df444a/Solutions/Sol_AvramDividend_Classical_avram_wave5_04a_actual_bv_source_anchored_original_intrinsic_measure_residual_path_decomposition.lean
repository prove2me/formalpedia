-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_anchored_original_intrinsic_measure_residual_path_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:36:53.951046+00:00
-- url     : https://prove2.me/submissions/9f6582ce-5ff3-42f9-ba35-c1efb50f7baf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual original BV Levy source sample path is anchored at
its genuine initial source value, with drift minus all intrinsic
negative source jumps minus an increasing downward residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ t : ℝ≥0,
        X.X t ω = X.X 0 ω + (t : ℝ) * X.drift -
          (∫⁻ p,
            (if (0 : ℝ≥0) < p.1 ∧ p.1 ≤ t then
              ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
          (R t - R 0) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro t
  have hinc := hinterval 0 t (by positivity)
  have hmass :=
    congrArg ENNReal.toReal
      (avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
        X ω 0 t)
  rw [← hmass] at hinc
  simp only [NNReal.coe_zero, sub_zero] at hinc
  linarith only [hinc]
