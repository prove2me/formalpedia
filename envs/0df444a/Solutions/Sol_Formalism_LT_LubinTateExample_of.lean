-- Prove2me | solution 1 for Formalism.LT.LubinTateExample_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:21.326375+00:00
-- url     : https://prove2.me/submissions/5e5cc3e5-0d57-454b-8532-a167587e608c

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Theorems.Thm_Formalism_LT_PadicP_lubinTateExample_of

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
open Formalism Formalism.LT
namespace Formalism.LT
theorem _root_.solution (hfg : Formalism.G.FunEqFormalGroup.{0}) (hh : Formalism.G.FunEqHom.{0})
    (hc : Formalism.G.FunEqCongr.{0}) : Formalism.G.LubinTateExample := PadicP.lubinTateExample_of hfg hh hc
end Formalism.LT
