-- Prove2me | solution 1 for Csg.skirmish_safe_le_AFGInner_safe_safe_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:23:02.802916+00:00
-- url     : https://prove2.me/submissions/68489e3c-f092-4afe-be1c-94e3edec9822

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmish_safe_subset_AFpre1_empty_safe_safe

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤
      skirmishCSG.AFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos) skirmishSafe := by
  intro s hs
  change s ∈
      (skirmishCSG.AFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe ∩ skirmishSafe) ∪
        (skirmishSafeᶜ ∩ skirmishCSG.Apre1 (∅ : Set SkirmishPos) skirmishSafe)
  exact Or.inl ⟨skirmish_safe_subset_AFpre1_empty_safe_safe hs, hs⟩
end Csg
