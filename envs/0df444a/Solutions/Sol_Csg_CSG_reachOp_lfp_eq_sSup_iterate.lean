-- Prove2me | solution 1 for Csg.CSG.reachOp_lfp_eq_sSup_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:46.052797+00:00
-- url     : https://prove2.me/submissions/55d1b5a5-4e88-4301-aa97-812274a44957

import Definitions.Def_Csg_ReachOp
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder
import Definitions.Def_Csg_ReachConverge
import Theorems.Thm_P2M_Csg_CSG_reachOp__ScottContinuous_01dcd6425b17

set_option autoImplicit true
open Csg
open Csg.CSG
open OmegaCompletePartialOrder Filter Topology
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    (C.reachOp goal hr).lfp = ⨆ n, (C.reachOp goal hr)^[n] ⊥ :=
  fixedPoints.lfp_eq_sSup_iterate (C.reachOp goal hr) (C.reachOp_ωScottContinuous goal hr)
end Csg.CSG
