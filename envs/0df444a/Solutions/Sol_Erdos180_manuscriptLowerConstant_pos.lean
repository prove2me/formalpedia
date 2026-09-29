-- Prove2me | solution 1 for Erdos180.manuscriptLowerConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:54:48.924052+00:00
-- url     : https://prove2.me/submissions/f2e0b87d-a2cc-43dc-ae01-33bc4d570d6f

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Erdos180
open Filter Finset SimpleGraph
open scoped Topology

theorem solution : 0 < manuscriptLowerConstant := by
  unfold manuscriptLowerConstant
  positivity
