-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:33.241827+00:00
-- url     : https://prove2.me/submissions/63fd5e67-dd3c-41a9-86de-cfb80af89d22

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_core
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_trivial_case

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
theorem _root_.solution (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) {a : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  by_cases hm : b - c ∈ L.lattice
  · exact trivial_case L b c hz hm
  · exact core L b c h1 hord hq hz he ho hs hadd ha hb hc hp hm
end Formalism.L2.Th1.F.ThreeTermRelation
