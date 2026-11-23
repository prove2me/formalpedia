-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.threeTermDenom_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:08.76824+00:00
-- url     : https://prove2.me/submissions/9567aa17-43f8-4b1b-a08f-34d27e482322

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_analyticAt

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
theorem _root_.solution (he : SigmaEntire) (z : ℂ) : AnalyticAt ℂ (threeTermDenom L b c) z :=
  ((sig_analyticAt L he (b + c) z).mul (sig_analyticAt L he (-b) z)).mul
    (sig_analyticAt L he (-c) z)
end Formalism.L2.Th1.F.ThreeTermRelation
