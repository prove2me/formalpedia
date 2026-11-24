-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:52:59.528861+00:00
-- url     : https://prove2.me/submissions/6c1b4a9c-53ea-4bf1-9f51-67ffdcb77e11

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermNum_eq_twistedGamma_of_sigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_twistedGamma_analyticAt_zero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_order_notMem
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_order_ge

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
theorem _root_.solution (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    0 ≤ meromorphicOrderAt (threeTermQuotient L b c) 0 := by
  have hN : 0 ≤ meromorphicOrderAt (nAux L b c) 0 := by
    have : nAux L b c =ᶠ[𝓝[≠] 0] frobeniusStickelbergerDetMulSigmaCube L b c := by
      filter_upwards [self_mem_nhdsWithin] with x hx using threeTermNum_eq_twistedGamma_of_sigmaZero L b c hz x hx
    rw [meromorphicOrderAt_congr this]
    exact (twistedGamma_analyticAt_zero L b c he).meromorphicOrderAt_nonneg
  have := threeTermQuotient_order_ge L b c he (z := 0) (k := 0)
    (sig_order_notMem L hord (by simpa using hp))
    (sig_order_notMem L hord (by simpa using hb))
    (sig_order_notMem L hord (by simpa using hc)) (by simpa using hN)
  simpa using this
end Formalism.L2.Th1.F.ThreeTermRelation
