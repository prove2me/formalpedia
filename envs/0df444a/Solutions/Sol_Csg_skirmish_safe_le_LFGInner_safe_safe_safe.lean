-- Prove2me | solution 1 for Csg.skirmish_safe_le_LFGInner_safe_safe_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:23:46.066348+00:00
-- url     : https://prove2.me/submissions/0a60ea35-7c97-45b9-8f0c-beabedc92dae

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_subset_LFpre1_safe_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.LFGInner skirmishSafe skirmishSafe skirmishSafe skirmishSafe := by
  intro s hs
  change s ∈ (skirmishCSG.LFpre1 skirmishSafe skirmishSafe skirmishSafe ∩ skirmishSafe) ∪
      (skirmishSafeᶜ ∩ skirmishCSG.Lpre1 skirmishSafe skirmishSafe)
  exact Or.inl ⟨skirmish_safe_subset_LFpre1_safe_safe_safe hs, hs⟩
end Csg
