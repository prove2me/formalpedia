-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:48:04.811917+00:00
-- url     : https://prove2.me/submissions/10c4b618-f7eb-4389-a585-6454ae458aa8

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original negative left-jump magnitude series is finite on
every bounded time interval under the actual BV hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (∑' (u : ℝ≥0),
        if s < u ∧ u ≤ t then
          ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) < ⊤ := by
  filter_upwards [avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual X hBV] with ω hω
  intro s t hst
  exact lt_of_le_of_lt (hω s t hst) ENNReal.ofReal_lt_top
