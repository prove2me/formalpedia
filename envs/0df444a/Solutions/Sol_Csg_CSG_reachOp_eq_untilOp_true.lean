-- Prove2me | solution 1 for Csg.CSG.reachOp_eq_untilOp_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:50.216248+00:00
-- url     : https://prove2.me/submissions/2af6cc1f-f259-4c61-86d3-c769e3b584e1

import Definitions.Def_Csg_CsgMonotone
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_UntilOp

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    C.reachOp goal hr = C.untilOp (fun _ => True) goal hr := by
  apply OrderHom.ext
  funext v
  funext s
  apply Subtype.ext
  change (C.reachOpFun goal hr v s : ℝ) = (C.untilOpFun (fun _ => True) goal hr v s : ℝ)
  by_cases hg : goal s
  · simp only [reachOpFun, untilOpFun, if_pos hg]
  · simp only [reachOpFun, untilOpFun, if_neg hg]
    rfl
end Csg.CSG
