-- Prove2me | solution 1 for Comp.CsgQ.reachOp_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:53:44.278462+00:00
-- url     : https://prove2.me/submissions/0f2efc03-4832-4633-a57f-68af5110ce91

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (C : CSG S A1 A2) (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (((C.reachOp goal hr) v s : ℝ))
      = if goal s then 1 else C.stageValue s (fun s' => ((v s' : ℝ))) := by
  change ((C.reachOpFun goal hr v s : ℝ))
    = if goal s then 1 else C.stageValue s (fun s' => ((v s' : ℝ)))
  unfold CSG.reachOpFun
  split_ifs <;> rfl
end Comp.CsgQ
