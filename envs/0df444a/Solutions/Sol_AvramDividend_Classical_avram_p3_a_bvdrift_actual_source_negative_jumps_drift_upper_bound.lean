-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:11.540856+00:00
-- url     : https://prove2.me/submissions/943d9398-8e89-4f5c-bb66-2ba699ca0b92

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV source has no upward variation beyond its physical drift:
its unremoved increasing residual only strengthens the upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      X.X t ω - X.X s ω +
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal ≤
      ((t : ℝ) - (s : ℝ)) * X.drift := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV] with ω hω
  obtain ⟨R, _hRdef, hRmono, hRinterval⟩ := hω
  intro s t hst
  have hRle : R s ≤ R t := hRmono hst
  have hInt := hRinterval s t hst
  linarith only [hRle, hInt]
