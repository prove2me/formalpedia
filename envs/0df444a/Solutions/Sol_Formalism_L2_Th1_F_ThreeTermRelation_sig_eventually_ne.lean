-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.sig_eventually_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:15.850852+00:00
-- url     : https://prove2.me/submissions/4035895a-cb2d-4605-ac1e-405167503a36

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_order_mem
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_order_notMem

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
theorem _root_.solution (he : SigmaEntire) (hord : SigmaOrder) (β z : ℂ) :
    ∀ᶠ x in 𝓝[≠] z, wSigma L (x + β) ≠ 0 := by
  refine (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (sig_analyticAt L he β z).meromorphicAt).1 ?_
  by_cases h : z + β ∈ L.lattice
  · rw [sig_order_mem L hord h]; exact WithTop.coe_ne_top
  · rw [sig_order_notMem L hord h]; exact WithTop.coe_ne_top
end Formalism.L2.Th1.F.ThreeTermRelation
