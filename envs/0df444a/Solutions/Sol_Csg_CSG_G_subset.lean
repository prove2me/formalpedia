-- Prove2me | solution 1 for Csg.CSG.G_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:53:46.759451+00:00
-- url     : https://prove2.me/submissions/1c8cb35f-3105-4f0f-81dc-87451c924f13

import Definitions.Def_Csg_BuchiOp
import Definitions.Def_Csg_QualitativeSure

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (safe : Set S) : C.G safe ⊆ safe := by
  intro s hs
  have h : C.GOrderHom safe (C.G safe) = C.G safe := (C.GOrderHom safe).map_gfp
  rw [← h] at hs
  exact hs.2
end Csg.CSG
