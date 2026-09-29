-- Prove2me | solution 1 for Erdos146.binaryEntropy_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T04:56:19.4269+00:00
-- url     : https://prove2.me/submissions/192bc74b-e661-4bdf-8fce-4f88912dcd1c

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (x : ℝ) : binaryEntropy x ≤ 1 := by
  unfold binaryEntropy
  apply (div_le_iff₀ log_two_pos).2
  simpa using (Real.binEntropy_le_log_two (p := x))
