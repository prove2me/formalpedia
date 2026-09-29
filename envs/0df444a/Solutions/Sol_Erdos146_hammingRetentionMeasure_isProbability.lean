-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:25:10.79326+00:00
-- url     : https://prove2.me/submissions/f95fad0e-9399-4f46-9965-c093cca30295

import Definitions.Def_erdos146_core2
import Mathlib.Probability.Distributions.SetBernoulli

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (dimension : ℕ) :
    MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) := by
  unfold hammingRetentionMeasure
  infer_instance
