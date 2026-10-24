-- Prove2me | solution 1 for AvramDividend.Classical.causal_bounded_continuous_contraction_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:02:41.21149+00:00
-- url     : https://prove2.me/submissions/da530e93-a668-421d-9344-b18461a12dd1

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal

/-- Banach fixed point on the weighted-resolvent function space. -/
theorem solution
    (T : BoundedContinuousFunction ℝ≥0 ℝ → BoundedContinuousFunction ℝ≥0 ℝ)
    (c : NNReal) (hc : c < 1) (hLip : LipschitzWith c T) :
    ∃ f : BoundedContinuousFunction ℝ≥0 ℝ, T f = f := by
  have hcontr : ContractingWith c T := ⟨hc, hLip⟩
  exact ⟨hcontr.fixedPoint, hcontr.fixedPoint_isFixedPt⟩
