-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_canonical_residual_nonnegative_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:07:48.846294+00:00
-- url     : https://prove2.me/submissions/e13c352a-916d-4fd4-9996-03ebdb5557c0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_canonical_residual_zero_at_origin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV drift-minus-jump canonical remainder is nonnegative
at every original sample-path time, starting exactly at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      0 ≤ ((t : ℝ) * X.drift - X.X t ω) -
        (∑' (u : ℝ≥0),
          if 0 < u ∧ u ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_canonical_remainder_monotone X hBV]
    with ω hω
  intro t
  have hmain := hω (show (0 : ℝ≥0) ≤ t from zero_le)
  have hzero :=
    avram_p3_a_bvdrift_original_canonical_residual_zero_at_origin X ω
  rw [← hzero]
  exact hmain
