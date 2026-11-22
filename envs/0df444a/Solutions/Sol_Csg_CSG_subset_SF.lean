-- Prove2me | solution 1 for Csg.CSG.subset_SF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:53:50.377036+00:00
-- url     : https://prove2.me/submissions/581f5883-1159-4f95-a122-313554a14b88

import Definitions.Def_Csg_BuchiOp
import Definitions.Def_Csg_QualitativeSure

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (b : Set S) : b ⊆ C.SF b := by
  intro s hs
  have h : C.SFOrderHom b (C.SF b) = C.SF b := (C.SFOrderHom b).map_lfp
  rw [← h]
  exact Or.inr hs
end Csg.CSG
