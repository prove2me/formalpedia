-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaAdd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:57.522554+00:00
-- url     : https://prove2.me/submissions/cd74c014-eb02-465b-a870-1a7d80c4c2a7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_periodic
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_sigma_zero
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_meromorphicAt
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_analyticAt
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_additionQuotient_order

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
open SigmaAdditionFormula
namespace Formalism.L2.Th1.F
theorem _root_.solution (hN : EllipticNoPole) (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero)
    (hs : SigmaSimple) (hq : SigmaQuasi) (hord : SigmaOrder) : SigmaAdd := by
  intro L z w hzL hwL
  obtain ⟨c, hc⟩ := hN L (additionQuotient L w) (additionQuotient_meromorphicAt L w he) (additionQuotient_periodic L w hq)
    (additionQuotient_order L w he ho hz hs hq hord)
  have hfz := hc z (additionQuotient_analyticAt L w he hz z hzL).continuousAt
  have hfw := hc w (additionQuotient_analyticAt L w he hz w hwL).continuousAt
  have hσz : wSigma L z ≠ 0 := fun h => hzL ((hz L z).1 h)
  have h0 := sigma_zero L hz
  rw [← hfw] at hfz
  unfold additionQuotient at hfz
  rw [sub_self, h0, mul_zero, zero_div, zero_add] at hfz
  have e : wSigma L (z + w) * wSigma L (z - w) / wSigma L z ^ 2 * wSigma L z ^ 2
      = wSigma L (z + w) * wSigma L (z - w) := div_mul_cancel₀ _ (pow_ne_zero 2 hσz)
  linear_combination (wSigma L z ^ 2) * hfz - e
end Formalism.L2.Th1.F
