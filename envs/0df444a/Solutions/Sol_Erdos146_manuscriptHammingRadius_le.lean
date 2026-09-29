-- Prove2me | solution 1 for Erdos146.manuscriptHammingRadius_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:44:31.054676+00:00
-- url     : https://prove2.me/submissions/1e9df0e9-e1ef-43f4-b362-c924160c1c79

import Definitions.Def_erdos146_core2
import Mathlib.Data.Real.Archimedean

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (dimension : ℕ) :
    (manuscriptHammingRadius dimension : ℝ) ≤
      tau * (dimension : ℝ) := by
  unfold manuscriptHammingRadius
  exact Nat.floor_le
    (mul_nonneg tau_pos.le (Nat.cast_nonneg dimension))
