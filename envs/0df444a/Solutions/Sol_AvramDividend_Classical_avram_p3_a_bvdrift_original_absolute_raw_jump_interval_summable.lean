-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:24:28.418227+00:00
-- url     : https://prove2.me/submissions/d97f5648-0913-448a-963d-5555c6281bec

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every original BV bounded-interval raw real negative-jump series
is absolutely summable, ready for Tannery dominated convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      Summable (fun u : ℝ≥0 =>
        |if s < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0|) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV]
    with ω hω
  intro s t hst
  exact (hω s t hst).1.abs
