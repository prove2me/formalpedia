-- Prove2me | solution 1 for Csg.CSG.B_empty_v1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:59:00.957328+00:00
-- url     : https://prove2.me/submissions/c4950fad-2cab-4817-8776-7f7fcebf80cd

import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (x : Set S) (s : S) : C.B (∅ : Set A1) x s = ∅ := by
  ext a2
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a1, ha1, _⟩
  exact ha1
end Csg.CSG
