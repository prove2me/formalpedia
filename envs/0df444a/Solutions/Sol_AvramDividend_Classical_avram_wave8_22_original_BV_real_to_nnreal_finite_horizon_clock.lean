-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_real_to_nnreal_finite_horizon_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:21:11.889202+00:00
-- url     : https://prove2.me/submissions/b67e877e-4673-487e-82f5-d05bffa623bc

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

/-- The actual deterministic stopped BV time clock, a pushforward of finite-interval Lebesgue measure, has finite mass. -/
theorem solution (T : ℝ≥0) (μT : Measure ℝ≥0)
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) :
  μT Set.univ < ∞ := by
  haveI hFiniteIcc :
      IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) :=
    Real.isFiniteMeasure_restrict_Icc 0 (T : ℝ)
  haveI hFiniteMap :
      IsFiniteMeasure (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal) :=
    Measure.isFiniteMeasure_map _ _
  rw [hTime]
  exact measure_lt_top _ _
