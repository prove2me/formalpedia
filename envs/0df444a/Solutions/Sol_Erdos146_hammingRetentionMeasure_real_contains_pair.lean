-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_real_contains_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:30:01.099259+00:00
-- url     : https://prove2.me/submissions/4383045e-8c73-4d46-965f-2377c96d0da6

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_finset

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension)
    (hdistinct : first ≠ second) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      hammingRetentionProbability dimension ^ 2 := by
  classical
  simpa [hdistinct] using
    hammingRetentionMeasure_real_contains_finset dimension {first, second}
