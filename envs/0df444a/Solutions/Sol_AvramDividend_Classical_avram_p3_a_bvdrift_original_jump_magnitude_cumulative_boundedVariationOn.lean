-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_magnitude_cumulative_boundedVariationOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:23:35.885888+00:00
-- url     : https://prove2.me/submissions/2662a9c6-3981-4371-a65b-4dfd9ead04bc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_monotone_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_monotone_real_path_compact_boundedVariation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV source cumulative negative jump magnitude process
has bounded total variation on each finite interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, a ≤ b →
      BoundedVariationOn (fun t : ℝ≥0 =>
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal)
        (Icc a b) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_real_jump_total_monotone_time X hBV]
    with ω hm
  intro a b hab
  exact avram_p3_a_bvdrift_monotone_real_path_compact_boundedVariation
    _ hm a b hab
