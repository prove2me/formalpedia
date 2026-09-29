-- Prove2me | solution 1 for Erdos180.extremalScale_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:54:07.384045+00:00
-- url     : https://prove2.me/submissions/f92dac60-ac0e-4306-918e-2bcd07d0d6d6

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Erdos180
open Filter Finset SimpleGraph
open scoped Topology

theorem solution (n : ℕ) :
    0 ≤ extremalScale n := by
  unfold extremalScale
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _
