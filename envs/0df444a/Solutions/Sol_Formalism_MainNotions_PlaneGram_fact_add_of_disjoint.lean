-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fact_add_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:44.501724+00:00
-- url     : https://prove2.me/submissions/43098209-0f5d-4379-bef7-0f31c2809a4f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} {α β : σ →₀ ℕ} (h : Disjoint α.support β.support) :
    fact (α + β) = fact α * fact β := by
  unfold fact
  exact Finsupp.prod_add_index_of_disjoint h _
end Formalism.MainNotions.PlaneGram
