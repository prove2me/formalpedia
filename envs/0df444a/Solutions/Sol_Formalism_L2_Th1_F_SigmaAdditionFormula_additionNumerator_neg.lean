-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.additionNumerator_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:51.189801+00:00
-- url     : https://prove2.me/submissions/81db9a28-c922-426a-9d49-cd7535c58b29

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
import Theorems.Thm_Formalism_L2_Th1_F_SigmaAdditionFormula_dslope_neg

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
open Formalism.L2.Th1.F.SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
namespace Formalism.L2.Th1.F.SigmaAdditionFormula
theorem _root_.solution (ho : SigmaOdd) (z : ℂ) : frobeniusStickelbergerDetMulSigmaCube L w (-z) = frobeniusStickelbergerDetMulSigmaCube L w z := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [dslope_neg L ho z, ho L z, L.weierstrassPExcept_neg, neg_zero,
    show -z + w = -(z - w) by ring, show -z - w = -(z + w) by ring, ho L (z - w), ho L (z + w)]
  ring
end Formalism.L2.Th1.F.SigmaAdditionFormula
