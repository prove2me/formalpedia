-- Prove2me | solution 1 for Csg.skirmish_safe_le_AFGInner_safe_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:47.281219+00:00
-- url     : https://prove2.me/submissions/bdea42a5-316c-4322-ae86-70340e731faa

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_subset_AFpre1_safe_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.AFGInner skirmishSafe skirmishSafe skirmishSafe skirmishSafe := by
  intro s hs
  change s ∈ (skirmishCSG.AFpre1 skirmishSafe skirmishSafe skirmishSafe ∩ skirmishSafe) ∪
      (skirmishSafeᶜ ∩ skirmishCSG.Apre1 skirmishSafe skirmishSafe)
  exact Or.inl ⟨skirmish_safe_subset_AFpre1_safe_safe_safe hs, hs⟩
end Csg
