-- Prove2me | solution 1 for Csg.CSG.B_empty_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:54:39.233811+00:00
-- url     : https://prove2.me/submissions/5d84e0fd-901f-445b-8964-cb49684ea98f

import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (v1 : Set A1) (s : S) : C.B v1 (∅ : Set S) s = ∅ := by
  ext a2
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a1, _, hne⟩
  rw [Set.inter_empty] at hne
  exact Set.not_nonempty_empty hne
end Csg.CSG
