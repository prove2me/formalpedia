-- Prove2me | solution 1 for Erdos146.tau_lt_one_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:07:33.437381+00:00
-- url     : https://prove2.me/submissions/3870d6d3-2809-47e5-abe8-b826f75d1998

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution : tau < (1 : ℝ) / 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  unfold tau
  nlinarith
