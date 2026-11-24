-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.prod_choose_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:35.6818+00:00
-- url     : https://prove2.me/submissions/12890f68-80bc-46fe-9fae-1e3be252c53a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel

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
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {σ : Type} [Fintype σ] (β M : σ →₀ ℕ) :
    ((β + M).prod fun x k => (k.choose (M x) : K)) = ((∏ x, (β x + M x).choose (M x) : ℕ) : K) := by
  simp only [Finsupp.prod, Finsupp.coe_add, Pi.add_apply, Nat.cast_prod]
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => ?_
  have h0 : β x = 0 ∧ M x = 0 := by simpa [Finsupp.mem_support_iff] using hx
  simp [h0.1, h0.2]
end Formalism.MainNotions.PlaneGram.TwistData
