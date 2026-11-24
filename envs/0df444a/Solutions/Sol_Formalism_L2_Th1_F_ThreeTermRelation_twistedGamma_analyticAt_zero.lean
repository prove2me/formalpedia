-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.twistedGamma_analyticAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:37:43.206125+00:00
-- url     : https://prove2.me/submissions/aee822ef-f983-4276-9b79-567e0d83ab5f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_analyticAt_dslope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.ThreeTermRelation
variable (L : PeriodPair) (b c : ℂ)
namespace Formalism.L2.Th1.F.ThreeTermRelation
theorem _root_.solution (he : SigmaEntire) : AnalyticAt ℂ (frobeniusStickelbergerDetMulSigmaCube L b c) 0 := by
  have h3 := analyticAt_dslope L he
  have h4 : AnalyticAt ℂ (wSigma L) 0 := (he L).analyticAt 0
  have h5 := L.analyticAt_weierstrassPExcept 0
  have h6 := L.analyticAt_derivWeierstrassPExcept 0
  unfold frobeniusStickelbergerDetMulSigmaCube
  fun_prop
end Formalism.L2.Th1.F.ThreeTermRelation
