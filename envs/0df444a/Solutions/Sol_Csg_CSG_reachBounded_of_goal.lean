-- Prove2me | solution 1 for Csg.CSG.reachBounded_of_goal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:24:37.99493+00:00
-- url     : https://prove2.me/submissions/411910dd-e511-4937-8bb0-120ab2b1794a

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BoundedReachability
import Theorems.Thm_Csg_CSG_reachBounded_zero
import Theorems.Thm_Csg_CSG_reachBounded_succ
attribute [local simp] Csg.CSG.reachBounded_zero

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal] (k : ℕ) {s : S}
    (hs : goal s) : C.reachBounded goal k s = 1 := by
  cases k with
  | zero => rw [reachBounded_zero, if_pos hs]
  | succ k => rw [reachBounded_succ, if_pos hs]
end Csg.CSG
