-- Prove2me | solution 1 for Csg.skirmish_safe_le_LGFOuter_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:36.675279+00:00
-- url     : https://prove2.me/submissions/9e07e242-82c3-4b53-92f8-f154e090df3a

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
import Theorems.Thm_OrderHom_map_map_bot_le_lfp
import Theorems.Thm_Csg_skirmish_home_le_LGFInnerFun_safe_bot
import Theorems.Thm_Csg_skirmish_safe_le_LGFInnerFun_safe_home

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    skirmishSafe ≤ skirmishCSG.LGFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by
  have hmono : skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ({SkirmishPos.home} : Set SkirmishPos) ≤
      skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        (skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
          (⊥ : Set SkirmishPos)) :=
    (skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe).mono
      skirmish_home_le_LGFInnerFun_safe_bot
  have hchain : skirmishSafe ≤
      skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        (skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
          (⊥ : Set SkirmishPos)) :=
    skirmish_safe_le_LGFInnerFun_safe_home.trans hmono
  exact hchain.trans (OrderHom.map_map_bot_le_lfp
    (skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe))
end Csg
