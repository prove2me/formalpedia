-- Prove2me | solution 1 for Csg.skirmish_wet_not_mem_Pre1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:13:57.335511+00:00
-- url     : https://prove2.me/submissions/134a9ce4-13d5-47e4-b051-0cc4125f6d27

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishK_support_wet


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (x : Set SkirmishPos) (hx : SkirmishPos.wet ∉ x) :
    SkirmishPos.wet ∉ skirmishCSG.Pre1 x := by
  intro hmem
  obtain ⟨a1, ha1⟩ := hmem
  have h := ha1 SniperMove.wait
  rw [skirmishK_support_wet] at h
  exact hx (Set.singleton_subset_iff.mp h)
end Csg
