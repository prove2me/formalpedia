-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_meromorphicAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:20.232401+00:00
-- url     : https://prove2.me/submissions/f776bb05-9b41-474f-bc63-f8a839b0a2e5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermDenom_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermNum_meromorphicAt

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
theorem _root_.solution (he : SigmaEntire) (z : ℂ) : MeromorphicAt (threeTermQuotient L b c) z :=
  (threeTermNum_meromorphicAt L b c he z).div (threeTermDenom_analyticAt L b c he z).meromorphicAt
end Formalism.L2.Th1.F.ThreeTermRelation
