-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.threeTermDenom_eventually_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:00.864618+00:00
-- url     : https://prove2.me/submissions/6552c282-bd88-465d-ac75-8f24e47a646b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_eventually_ne

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
theorem _root_.solution (he : SigmaEntire) (hord : SigmaOrder) (z : ℂ) :
    ∀ᶠ x in 𝓝[≠] z, threeTermDenom L b c x ≠ 0 := by
  filter_upwards [sig_eventually_ne L he hord (b + c) z, sig_eventually_ne L he hord (-b) z,
    sig_eventually_ne L he hord (-c) z] with x h1 h2 h3
  exact mul_ne_zero (mul_ne_zero h1 h2) h3
end Formalism.L2.Th1.F.ThreeTermRelation
