-- Prove2me | solution 1 for AvramDividend.Classical.compactTest_nnreal_uniformBound_finiteLintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:10:49.775603+00:00
-- url     : https://prove2.me/submissions/d8c1720c-0172-4026-9837-6a18ad7c1066

import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- Compact nonnegative tests have a finite constant bound under finite measures. -/
theorem solution

    {Ω Y : Type*} [MeasurableSpace Ω] [TopologicalSpace Y]
    (P : Measure Ω) (hP : P Set.univ ≠ ⊤)
    (f : CompactlySupportedContinuousMap Y ℝ≥0) :
    (∀ y : Y,
      ((f y : ℝ≥0) : ℝ≥0∞) ≤
      ((nndist (0 : BoundedContinuousFunction Y ℝ≥0)
        f.toBoundedContinuousFunction : ℝ≥0) : ℝ≥0∞)) ∧
    (∫⁻ _ : Ω,
      ((nndist (0 : BoundedContinuousFunction Y ℝ≥0)
        f.toBoundedContinuousFunction : ℝ≥0) : ℝ≥0∞) ∂P) ≠ ⊤ := by
  constructor
  · intro y
    exact_mod_cast
      (BoundedContinuousFunction.apply_le_nndist_zero
        f.toBoundedContinuousFunction y)
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hP
