-- Prove2me | solution 1 for Formalism.LT.PadicP.funEqPadic_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:51.946281+00:00
-- url     : https://prove2.me/submissions/b9fb1d51-7500-467f-9598-527eb9d080be

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Theorems.Thm_Formalism_LT_PadicP_frobLiftPadic
import Theorems.Thm_Formalism_LT_PadicP_map_map_unitBall

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
theorem _root_.solution (hfg : FunEqFormalGroup.{0}) : FunEqPadic := by
  intro p _ f h0 h1 hf
  obtain ⟨F, hF⟩ := hfg ℚ_[p] p p (RingHom.id _) (frobLiftPadic p) f h0 h1 hf
  exact ⟨F.map (unitBallEquiv p).toRingHom, by rw [map_map_unitBall]; exact hF⟩
end Formalism.LT.PadicP
