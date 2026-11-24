-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.approx_of_trunc_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:40:53.26528+00:00
-- url     : https://prove2.me/submissions/ede2c0e6-f4e2-4b98-8cec-03727f2985e8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_natCast_nonneg_monomial_order_segments
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_sum_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_mul_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_prod_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_CostOK_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cost_prod_choose_gen

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
theorem _root_.solution (hC : CostOK TotallyRealRoots) {κ : Type} [Fintype κ] (u : κ → (σ →₀ ℕ) → ℕ)
    (hu : ∀ a k, TotallyRealRoots k (fun α => ((u a α).choose k : K)))
    (T : Finset (κ → ℕ)) (lam : (κ → ℕ) → K) {c n : ℕ}
    (hlam : ∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ a, m a ≤ n) (f : (σ →₀ ℕ) → K)
    (hf : ∀ α, (c : WithTop ℚ) ≤ v (f α - binomComb T lam (fun a => u a α))) :
    ∃ g : (σ →₀ ℕ) → K, (∀ α, 0 ≤ v (g α)) ∧ (∀ α, (c : WithTop ℚ) ≤ v (f α - g α)) ∧ TotallyRealRoots n g := by
  refine ⟨fun α => binomComb T lam (fun a => u a α), fun α => ?_, hf, ?_⟩
  · show 0 ≤ v (∑ m ∈ T, lam m * ∏ a, ((u a α).choose (m a) : K))
    exact v_sum_nonneg _ _ (fun m hm => v_mul_nonneg (hlam m hm).1
      (v_prod_nonneg _ _ (fun a _ => v_natCast_nonneg_monomial_order_segments _)))
  · exact hC.sum T n (fun m α => lam m * ∏ a, ((u a α).choose (m a) : K))
      (fun m hm => hC.smul n (lam m) _
        (hC.mono _ n _ (hlam m hm).2 (cost_prod_choose_gen hC.one hC.mul u hu m)))
end Formalism.MainNotions.PlaneGram
