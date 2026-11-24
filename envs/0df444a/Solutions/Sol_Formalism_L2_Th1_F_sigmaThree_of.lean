-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaThree_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:10.175273+00:00
-- url     : https://prove2.me/submissions/f3b0a93a-f25e-484e-a4a5-d6cbad9906eb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_trivial_case
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_step
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_det_eq
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermDet_cycle

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
open ThreeTermRelation
namespace Formalism.L2.Th1.F
theorem _root_.solution (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) : SigmaThree := by
  intro L a b c ha hb hc
  rw [det_eq]
  by_cases hp1 : b + c ∈ L.lattice
  · by_cases hp2 : c + a ∈ L.lattice
    · have hm : a - b ∈ L.lattice := by
        have := L.lattice.sub_mem hp2 hp1
        convert this using 1; ring
      have := trivial_case L a b hz (a := c) hm
      rw [threeTermDet_cycle, threeTermDet_cycle]
      have e : c + a + b = a + b + c := by ring
      rw [e] at this
      linear_combination this
    · have := step L c a h1 hord hq hz he ho hs hadd hb hc ha hp2
      rw [threeTermDet_cycle]
      have e : b + c + a = a + b + c := by ring
      rw [e] at this
      linear_combination this
  · exact step L b c h1 hord hq hz he ho hs hadd ha hb hc hp1
end Formalism.L2.Th1.F
