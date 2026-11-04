-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:57:38.687297+00:00
-- url     : https://prove2.me/submissions/73459ac4-add3-4e93-9a88-34d2c9dd6d48

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every raw original negative left-jump sum has nonnegative sign, pathwise.
This sign assertion does not assume BV summability or an auxiliary process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t) :
    0 ≤ (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
      else 0) := by
  have hpoint (u : ℝ≥0) :
      0 ≤ (if s < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by
    by_cases hu : s < u ∧ u ≤ t
    · have hsnonneg : (0 : ℝ≥0) ≤ s := zero_le
      have hpos : 0 < u := lt_of_le_of_lt hsnonneg hu.1
      simpa [hu] using
        (avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
          X ω u hpos).1
    · simp [hu]
  exact tsum_nonneg hpoint
