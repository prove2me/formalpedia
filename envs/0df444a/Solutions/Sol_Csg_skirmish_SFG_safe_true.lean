-- Prove2me | solution 1 for Csg.skirmish_SFG_safe_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:06.697263+00:00
-- url     : https://prove2.me/submissions/4e410554-8ced-441f-92a5-cde8a1eb2c7c

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishSafe_eq_G
import Theorems.Thm_Csg_CSG_subset_SF


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : SkirmishPos.hide ∈ skirmishCSG.SFG skirmishSafe := by
  change SkirmishPos.hide ∈ skirmishCSG.SF (skirmishCSG.G skirmishSafe)
  rw [skirmishSafe_eq_G]
  exact skirmishCSG.subset_SF skirmishSafe (by decide)
end Csg
