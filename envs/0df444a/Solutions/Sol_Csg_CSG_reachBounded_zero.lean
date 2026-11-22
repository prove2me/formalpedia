-- Prove2me | solution 1 for Csg.CSG.reachBounded_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:33.960398+00:00
-- url     : https://prove2.me/submissions/0baf7c16-d071-47b4-b53b-ac6375e8d0a4

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BoundedReachability

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal] (s : S) :
    C.reachBounded goal 0 s = if goal s then 1 else 0 := rfl
end Csg.CSG
