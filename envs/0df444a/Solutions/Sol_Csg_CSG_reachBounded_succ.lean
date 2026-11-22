-- Prove2me | solution 1 for Csg.CSG.reachBounded_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:47:50.165593+00:00
-- url     : https://prove2.me/submissions/2b997b9c-e5eb-4b16-b44e-03641082231c

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BoundedReachability

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal] (k : ℕ) (s : S) :
    C.reachBounded goal (k + 1) s =
      if goal s then 1 else C.stageValue s (C.reachBounded goal k) := rfl
end Csg.CSG
