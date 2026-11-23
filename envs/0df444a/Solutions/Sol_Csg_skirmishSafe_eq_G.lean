-- Prove2me | solution 1 for Csg.skirmishSafe_eq_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:10:47.065027+00:00
-- url     : https://prove2.me/submissions/4c2c61d4-b8a8-49d6-b2d2-ebaa94ae4ae1

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishSafe_pre1
import Theorems.Thm_Csg_CSG_G_subset


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : skirmishCSG.G skirmishSafe = skirmishSafe := by
  apply le_antisymm (skirmishCSG.G_subset skirmishSafe)
  have hle : skirmishSafe ≤ skirmishCSG.GOrderHom skirmishSafe skirmishSafe := by
    intro s hs
    exact ⟨skirmishSafe_pre1 hs, hs⟩
  exact (skirmishCSG.GOrderHom skirmishSafe).le_gfp hle
end Csg
