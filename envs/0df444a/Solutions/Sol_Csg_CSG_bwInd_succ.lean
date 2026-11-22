-- Prove2me | solution 1 for Csg.CSG.bwInd_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:44:40.151472+00:00
-- url     : https://prove2.me/submissions/21fce38d-8ad8-4e44-9fb6-9ac2a28c0be7

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BackwardInduction

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (rFin : S → ℝ) (n : ℕ) (s : S) :
    C.bwInd rFin (n + 1) s = C.stageValue s (C.bwInd rFin n) := rfl
end Csg.CSG
