-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.Slope.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:56.921375+00:00
-- url     : https://prove2.me/submissions/7b6fc96b-0cfe-4162-9cd4-3d1b9090d31b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_sum_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_mul_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_trunc
import Theorems.Thm_Formalism_MainNotions_PlaneGram_CostOK_sum

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
namespace Formalism.MainNotions.PlaneGram
namespace Slope
theorem _root_.solution {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} (hC : CostOK TotallyRealRoots) {c : ℕ}
    {f : (σ →₀ ℕ) → K} (sf : Slope v TotallyRealRoots c f) :
    ∃ g : (σ →₀ ℕ) → K, (∀ α, 0 ≤ v (g α)) ∧ (∀ α, (c : WithTop ℚ) ≤ v (f α - g α)) ∧
      TotallyRealRoots (6 * c) g := by
  obtain ⟨ι, hι, lam, n, b, h0, hn, h2, h3, h4⟩ := sf.trunc
  refine ⟨fun α => ∑ k, lam k * b k α,
    fun α => v_sum_nonneg _ _ (fun k _ => v_mul_nonneg (h0 k) (h3 k α)), h4, ?_⟩
  exact hC.sum Finset.univ (6 * c) (fun k α => lam k * b k α)
    (fun k _ => hC.smul _ (lam k) _ (hC.mono _ _ _ (hn k) (h2 k)))
end Slope
end Formalism.MainNotions.PlaneGram
