-- Prove2me | solution 1 for Formalism.ValuationGridEstimates.norm_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:58.960522+00:00
-- url     : https://prove2.me/submissions/38711366-d685-4902-afe4-fe9597c811a6

import Definitions.Def_Formalism_TowerValuationBounds_HermitianSumValuationBound
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ValuationGridEstimates
open Finset
namespace Formalism.ValuationGridEstimates
theorem _root_.solution : NormProductRatio := by
  intro K _ Ac Ω2 L L0 lo hi hA hΩ
  rw [prod_div_distrib, div_div_div_cancel_right₀ hΩ, mul_div_mul_left _ _ hA]
end Formalism.ValuationGridEstimates
