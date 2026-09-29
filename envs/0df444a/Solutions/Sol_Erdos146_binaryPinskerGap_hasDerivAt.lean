-- Prove2me | solution 1 for Erdos146.binaryPinskerGap_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T04:58:23.748+00:00
-- url     : https://prove2.me/submissions/8f6cbd23-1b32-46da-b052-b8754dab5d11

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGap (binaryPinskerGapDeriv q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hderiv :=
    ((Real.hasDerivAt_binEntropy hqzero hqone).const_sub (Real.log 2)).sub
      ((hlinear.pow 2).div_const 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGap, binaryPinskerGapDeriv]; ring)
