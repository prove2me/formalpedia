-- Prove2me | solution 1 for Formalism.L2.Th1.F.ThreeTermRelation.threeTermQuotient_order_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:02.073595+00:00
-- url     : https://prove2.me/submissions/79a36a98-f150-4de2-bce9-b44aa17f8174

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_order_mem
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_sig_order_notMem
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermNum_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermQuotient_order_ge
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_one_le_order
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermNum_eq_zero_left
import Theorems.Thm_Formalism_L2_Th1_F_ThreeTermRelation_threeTermNum_eq_zero_right

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
theorem _root_.solution (he : SigmaEntire) (hord : SigmaOrder) (hm : b - c ∉ L.lattice) {z : ℂ}
    (hzL : z ∉ L.lattice) {m1 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L (w + (b + c))) z = (m1 : WithTop ℤ)) :
    ((-m1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have han := threeTermNum_analyticAt L b c he z hzL
  by_cases hb : z + -b ∈ L.lattice
  · have hc : z + -c ∉ L.lattice := fun hc => hm (by
      have := L.lattice.sub_mem hc hb
      convert this using 1; ring)
    refine threeTermQuotient_order_ge L b c he h1 (sig_order_mem L hord hb) (sig_order_notMem L hord hc) ?_
    have := one_le_order han (threeTermNum_eq_zero_left L b c hb)
    convert this using 2; ring
  · by_cases hc : z + -c ∈ L.lattice
    · refine threeTermQuotient_order_ge L b c he h1 (sig_order_notMem L hord hb) (sig_order_mem L hord hc) ?_
      have := one_le_order han (threeTermNum_eq_zero_right L b c hc)
      convert this using 2; ring
    · refine threeTermQuotient_order_ge L b c he h1 (sig_order_notMem L hord hb) (sig_order_notMem L hord hc) ?_
      have := han.meromorphicOrderAt_nonneg
      convert this using 1
      simp
end Formalism.L2.Th1.F.ThreeTermRelation
