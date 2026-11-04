-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:30:15.621481+00:00
-- url     : https://prove2.me/submissions/987b122f-d7cb-4553-b572-1ae2890bff03

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_left_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_monotone_path_continuous_of_leftLim_and_right

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- After removing the genuine original BV source's negative left jumps,
the physical-drift remainder is continuous at every positive time a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ContinuousAt (fun s : ℝ≥0 =>
        (((s : ℝ) * X.drift - X.X s ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) t := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV,
     avram_p3_a_bvdrift_original_raw_removed_residual_left_continuous X hBV,
     avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous X hBV]
    with ω hm hl hr
  intro t ht
  exact avram_p3_a_bvdrift_monotone_path_continuous_of_leftLim_and_right
    _ hm t ht (hl t ht) (hr t)
