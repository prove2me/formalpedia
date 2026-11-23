-- Prove2me | solution 1 for Csg.skirmish_Apre1_safe_top_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:10:19.772341+00:00
-- url     : https://prove2.me/submissions/ce8f5e35-25b0-4f6f-b5a7-302b22219bef

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_wet_not_mem_Apre1

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishCSG.Apre1 skirmishSafe (⊤ : Set SkirmishPos) ⊆ skirmishSafe := by
  intro s hs
  cases s with
  | hide => decide
  | home => decide
  | wet => exact absurd hs (skirmish_wet_not_mem_Apre1 skirmishSafe ⊤ (by decide))
end Csg
