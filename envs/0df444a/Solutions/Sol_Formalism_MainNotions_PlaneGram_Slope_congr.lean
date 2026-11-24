-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.Slope.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:15.761284+00:00
-- url     : https://prove2.me/submissions/06fd3235-8ea8-4226-9ee1-9d6f00d0f56e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_add_ge

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
open Formalism.MainNotions.PlaneGram.Slope
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}
namespace Formalism.MainNotions.PlaneGram.Slope
theorem _root_.solution {f g : (σ →₀ ℕ) → K} (h : ∀ α, (c : WithTop ℚ) ≤ v (f α - g α))
    (hf : Slope v TotallyRealRoots c f) : Slope v TotallyRealRoots c g := by
  obtain ⟨ι, hι, lam, n, b, h1, h2, h3, h4⟩ := hf
  refine ⟨ι, hι, lam, n, b, h1, h2, h3, fun α => ?_⟩
  have e : g α - ∑ k, lam k * b k α = (g α - f α) + (f α - ∑ k, lam k * b k α) := by ring
  rw [e]
  refine v_add_ge ?_ (h4 α)
  rw [AddValuation.map_sub_swap]
  exact h α
end Formalism.MainNotions.PlaneGram.Slope
