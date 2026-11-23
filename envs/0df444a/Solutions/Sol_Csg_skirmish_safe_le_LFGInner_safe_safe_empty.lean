-- Prove2me | solution 1 for Csg.skirmish_safe_le_LFGInner_safe_safe_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:05.324494+00:00
-- url     : https://prove2.me/submissions/9bb73bce-09da-4dc3-8df9-dd60523ad22a

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_subset_LFpre1_empty_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤
      skirmishCSG.LFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos) skirmishSafe := by
  intro s hs
  change s ∈
      (skirmishCSG.LFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe ∩ skirmishSafe) ∪
        (skirmishSafeᶜ ∩ skirmishCSG.Lpre1 (∅ : Set SkirmishPos) skirmishSafe)
  exact Or.inl ⟨skirmish_safe_subset_LFpre1_empty_safe_safe hs, hs⟩
end Csg
