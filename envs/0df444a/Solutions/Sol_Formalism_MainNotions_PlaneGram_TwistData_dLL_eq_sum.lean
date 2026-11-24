-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.dLL_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:28.049781+00:00
-- url     : https://prove2.me/submissions/8e5eff8b-a310-4293-818b-eb73e8a82831

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution : D.dLL j = ∑ a, D.dB (D.eB j a) := by
  unfold dLL
  rw [← Finset.sum_coe_sort (D.LLj j)]
  exact (Equiv.sum_comp (D.LLj j).equivFin.symm (fun x => D.dB x.1)).symm
end Formalism.MainNotions.PlaneGram.TwistData
