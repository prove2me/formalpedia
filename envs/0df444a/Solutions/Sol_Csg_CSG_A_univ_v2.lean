-- Prove2me | solution 1 for Csg.CSG.A_univ_v2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:54:41.565725+00:00
-- url     : https://prove2.me/submissions/104b10e6-54fb-49ff-bf86-73eea322a53a

import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (y : Set S) (s : S) : C.A (Set.univ : Set A2) y s = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a1 a2
  exact Or.inl (Set.mem_univ a2)
end Csg.CSG
