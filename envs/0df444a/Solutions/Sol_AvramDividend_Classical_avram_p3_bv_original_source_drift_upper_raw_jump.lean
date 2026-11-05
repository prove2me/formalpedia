-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_source_drift_upper_raw_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:45:55.150791+00:00
-- url     : https://prove2.me/submissions/0e55f173-995f-4e63-bfb5-5f9a832617af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_raw_jump_interval_nonnegative_remainder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original BV residual has the favourable sign for an upper generator
budget: physical drift dominates the source increment plus all raw losses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      X.X t ω - X.X s ω +
        (∑' u : ℝ≥0,
          if s < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0) ≤
        ((t : ℝ) - (s : ℝ)) * X.drift := by
  filter_upwards
    [avram_p3_a_bvdrift_source_raw_jump_interval_nonnegative_remainder X hBV]
      with ω hω
  intro s t hst
  obtain ⟨r, hr, heq⟩ := hω s t hst
  nlinarith [heq]
