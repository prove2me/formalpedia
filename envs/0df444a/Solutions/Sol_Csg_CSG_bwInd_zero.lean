-- Prove2me | solution 1 for Csg.CSG.bwInd_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:22.500524+00:00
-- url     : https://prove2.me/submissions/f959344c-d82a-463e-83d7-3786e66157d8

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BackwardInduction

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (rFin : S → ℝ) : C.bwInd rFin 0 = rFin := rfl
end Csg.CSG
