-- Prove2me | solution 1 for Formalism.LT.FunEqGroup_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:00:51.123047+00:00
-- url     : https://prove2.me/submissions/163ce8d3-46c0-4540-b741-48819c902b66

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
import Theorems.Thm_P2M_Formalism_LT_Asm_FunEqGroup_of__ab8c5b9f22dd

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
theorem _root_.solution (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} :=
  Formalism.LT.Asm.FunEqGroup_of' h1 h2 h3 hk
end Formalism.LT
