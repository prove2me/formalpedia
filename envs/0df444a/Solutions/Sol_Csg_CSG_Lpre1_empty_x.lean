-- Prove2me | solution 1 for Csg.CSG.Lpre1_empty_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:29:15.708286+00:00
-- url     : https://prove2.me/submissions/88c6972e-8ef6-4361-b4e5-a938e0294fa8

import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Theorems.Thm_Csg_CSG_B_empty_x


set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (y : Set S) : C.Lpre1 (∅ : Set S) y = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  have heq : C.B (C.LW ∅ y s) (∅ : Set S) s = (Set.univ : Set A2) := hs
  rw [C.B_empty_x (C.LW ∅ y s) s] at heq
  have hmem : (Classical.arbitrary A2) ∈ (Set.univ : Set A2) := Set.mem_univ _
  rw [← heq] at hmem
  exact hmem
end Csg.CSG
