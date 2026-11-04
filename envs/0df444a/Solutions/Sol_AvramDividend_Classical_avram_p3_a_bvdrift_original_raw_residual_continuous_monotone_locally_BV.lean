-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_residual_continuous_monotone_locally_BV
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:59:21.709907+00:00
-- url     : https://prove2.me/submissions/2780b402-b773-4fe2-a682-b3505cde5652

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_boundedVariationOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual source BV jump-removed residual has simultaneous path regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ≥0 =>
        (((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) ∧
      Monotone (fun t : ℝ≥0 =>
        (((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        BoundedVariationOn (fun t : ℝ≥0 =>
          (((t : ℝ) * X.drift - X.X t ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))
          (Icc a b)) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time X hBV,
      avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV,
      avram_p3_a_bvdrift_original_raw_removed_residual_boundedVariationOn X hBV]
    with ω hcont hmono hvar
  exact ⟨hcont, hmono, hvar⟩
