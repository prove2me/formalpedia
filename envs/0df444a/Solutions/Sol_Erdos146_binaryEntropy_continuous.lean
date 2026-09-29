-- Prove2me | solution 1 for Erdos146.binaryEntropy_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T04:57:42.195593+00:00
-- url     : https://prove2.me/submissions/71dd2283-f40e-43c6-9564-0dbdf859d02d

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

@[fun_prop] theorem solution : Continuous binaryEntropy := by
  exact Real.binEntropy_continuous.div_const _
