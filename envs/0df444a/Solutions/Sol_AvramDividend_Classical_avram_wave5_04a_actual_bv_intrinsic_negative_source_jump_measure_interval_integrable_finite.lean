-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_source_jump_measure_interval_integrable_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:00:27.276584+00:00
-- url     : https://prove2.me/submissions/b7ccfdbe-4064-41d2-8f5a-f5e122af46a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_intrinsic_negative_jump_integral_le_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On almost every actual original BV Levy path, the intrinsic source
negative left-jump magnitude integral is finite on every compact
time interval. This is a corollary of the genuine residual domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (∫⁻ p,
        (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≠ ⊤ := by
  filter_upwards
    [avram_wave4_04a_bv_actual_interval_intrinsic_negative_jump_integral_le_residual
      X hBV] with ω hω
  intro s t hst
  have hle := hω s t hst
  exact ne_top_of_le_ne_top (by simp) hle
