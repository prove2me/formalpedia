-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_source_continuous_on_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:36:54.014599+00:00
-- url     : https://prove2.me/submissions/da6e3974-2a28-4a04-b748-da09d4195d18

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonjump_iff_continuous_at

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal source jump measure vanishes on an interval precisely when
the unchanged original sample path is continuous at each time in it. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) = 0 ↔
      ∀ u : ℝ≥0, u ∈ Ioc s t →
        ContinuousAt (fun v : ℝ≥0 => X.X v ω) u := by
  rw [avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
    X ω s t]
  constructor
  · intro h u hu
    exact
      (avram_wave4_04a_actual_source_nonjump_iff_continuous_at
        X ω u (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hu.1)).mp (h u hu)
  · intro h u hu
    exact
      (avram_wave4_04a_actual_source_nonjump_iff_continuous_at
        X ω u (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hu.1)).mpr (h u hu)
