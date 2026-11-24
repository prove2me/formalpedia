-- Prove2me | solution 1 for Formalism.LT.PadicP.map_map_unitBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:40.861508+00:00
-- url     : https://prove2.me/submissions/f963eb68-fc58-464b-b1dd-68d68e2db99a

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul

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
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
namespace Formalism.LT.PadicP
theorem _root_.solution (p : ℕ) [Fact p.Prime] (F : FormalGroup (unitBall ℚ_[p])) :
    (F.map (unitBallEquiv p).toRingHom).map PadicInt.Coe.ringHom = F.map (unitBall ℚ_[p]).subtype := by
  unfold FormalGroup.map
  congr 1
end Formalism.LT.PadicP
