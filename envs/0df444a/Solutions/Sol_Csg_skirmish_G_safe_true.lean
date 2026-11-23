-- Prove2me | solution 1 for Csg.skirmish_G_safe_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:00.854533+00:00
-- url     : https://prove2.me/submissions/a5bea8a9-f6f1-476d-b73f-5556a3952482

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_Csg_skirmishSafe_eq_G

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : SkirmishPos.hide ∈ skirmishCSG.G skirmishSafe := by
  rw [skirmishSafe_eq_G]
  decide
end Csg
