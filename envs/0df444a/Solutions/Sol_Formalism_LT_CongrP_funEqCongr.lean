-- Prove2me | solution 1 for Formalism.LT.CongrP.funEqCongr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:04.206251+00:00
-- url     : https://prove2.me/submissions/fb129d9b-1bee-4f45-987c-692b1a204ba1

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
import Theorems.Thm_Formalism_LT_CongrP_fwd
import Theorems.Thm_Formalism_LT_CongrP_bwd

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
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
namespace Formalism.LT.CongrP
theorem _root_.solution (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) :
    Formalism.G.FunEqCongr.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfe α β hα0 hβ0 hα hβ r hr
  exact ⟨fwd h5 h6 hS hf0 hfe hα0 hβ0 hα hβ hr, bwd h5 h6 hS hf0 hf1 hfe hα0 hβ0 hα hβ hr⟩
end Formalism.LT.CongrP
