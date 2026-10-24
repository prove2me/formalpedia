-- Prove2me | solution 1 for AvramDividend.Classical.causal_BCF_contraction_of_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:53:12.420045+00:00
-- url     : https://prove2.me/submissions/0fbaba74-d6b5-4c9c-b0ca-8c74cb2f61f9

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal

/-- A strict uniform pointwise BCF estimate gives a Banach contraction. -/
theorem solution
    (T : BoundedContinuousFunction ℝ≥0 ℝ →
      BoundedContinuousFunction ℝ≥0 ℝ)
    (a m : ℝ) (ha : 0 < a) (hm0 : 0 ≤ m) (hma : m < a)
    (hPoint : ∀ (f h : BoundedContinuousFunction ℝ≥0 ℝ)
      (x : ℝ≥0), dist (T f x) (T h x) ≤ (m / a) * dist f h) :
    ∃ c : NNReal, c < 1 ∧ LipschitzWith c T := by
  let c : NNReal := ⟨m / a, div_nonneg hm0 ha.le⟩
  refine ⟨c, ?_, ?_⟩
  · change m / a < 1
    exact (div_lt_one ha).mpr hma
  · apply LipschitzWith.of_dist_le_mul
    intro f h
    have hC : 0 ≤ (c : ℝ) * dist f h :=
      mul_nonneg c.property dist_nonneg
    apply (BoundedContinuousFunction.dist_le hC).2
    intro x
    exact hPoint f h x
