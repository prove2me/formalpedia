-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaAdditionFormula.dslope_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:24:58.358967+00:00
-- url     : https://prove2.me/submissions/d56f0a40-364f-4831-843d-7c356ab73ab7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd

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
theorem _root_.solution (ho : SigmaOdd) (z : ℂ) : dslope (wSigma L) 0 (-z) = dslope (wSigma L) 0 z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [neg_zero]
  · have h0 : wSigma L 0 = 0 := by
      have := ho L 0
      rw [neg_zero] at this
      linear_combination this / 2
    rw [dslope_of_ne _ (neg_ne_zero.2 hz0), dslope_of_ne _ hz0, slope_def_field, slope_def_field,
      ho L z, h0, sub_zero, sub_zero, sub_zero, sub_zero, neg_div_neg_eq]
end Formalism.L2.Th1.F.SigmaAdditionFormula
