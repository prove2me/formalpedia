-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.approx_of_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:04.529625+00:00
-- url     : https://prove2.me/submissions/38fc6ced-159e-470c-a774-c50614f7c316

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_approx_of_trunc_gen

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
theorem _root_.solution [Fintype σ] (hC : CostOK TotallyRealRoots)
    (hch : ∀ x k, TotallyRealRoots k (fun α => ((α x).choose k : K)))
    (T : Finset (σ → ℕ)) (lam : (σ → ℕ) → K) {c n : ℕ}
    (hlam : ∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ n) (f : (σ →₀ ℕ) → K)
    (hf : ∀ α, (c : WithTop ℚ) ≤ v (f α - binomComb T lam (fun x => α x))) :
    ∃ g : (σ →₀ ℕ) → K, (∀ α, 0 ≤ v (g α)) ∧ (∀ α, (c : WithTop ℚ) ≤ v (f α - g α)) ∧ TotallyRealRoots n g := by
  exact approx_of_trunc_gen hC (fun x α => α x) hch T lam hlam f hf
end Formalism.MainNotions.PlaneGram
