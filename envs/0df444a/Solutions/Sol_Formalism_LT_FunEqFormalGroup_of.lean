-- Prove2me | solution 1 for Formalism.LT.FunEqFormalGroup_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:45.853353+00:00
-- url     : https://prove2.me/submissions/09b62580-80de-450f-b3f1-fd23b80f3383

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
import Theorems.Thm_P2M_Formalism_LT_Asm_FunEqFormalGroup_of__af71105fe109

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT
namespace Formalism.LT
theorem _root_.solution (hg : Formalism.G.FunEqGroup.{u}) : Formalism.G.FunEqFormalGroup.{u} :=
  Formalism.LT.Asm.FunEqFormalGroup_of' hg
end Formalism.LT
