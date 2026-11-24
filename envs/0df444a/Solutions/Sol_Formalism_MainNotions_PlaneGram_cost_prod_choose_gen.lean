-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cost_prod_choose_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:27.289649+00:00
-- url     : https://prove2.me/submissions/fb249ef9-487c-4550-ba9d-23f1009a0851

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cost_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (h1 : TotallyRealRoots 0 (fun _ => 1))
    (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {κ : Type} [Fintype κ] (u : κ → (σ →₀ ℕ) → ℕ)
    (hu : ∀ a k, TotallyRealRoots k (fun α => ((u a α).choose k : K))) (m : κ → ℕ) :
    TotallyRealRoots (∑ a, m a) (fun α => ∏ a, ((u a α).choose (m a) : K)) := by
  exact cost_prod h1 hmul Finset.univ m (fun a α => ((u a α).choose (m a) : K))
    (fun a _ => hu a (m a))
end Formalism.MainNotions.PlaneGram
