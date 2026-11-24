-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.CostOK.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:43.922933+00:00
-- url     : https://prove2.me/submissions/84d44c57-9b7e-4928-b444-efdb73f62e80

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_one
import Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_mul

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
open Formalism.MainNotions.PlaneGram.CostOK
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}
namespace Formalism.MainNotions.PlaneGram.CostOK
theorem _root_.solution (hC : CostOK TotallyRealRoots) {κ : Type} (s : Finset κ) (n : κ → ℕ) (f : κ → (σ →₀ ℕ) → K)
    (h : ∀ i ∈ s, TotallyRealRoots (n i) (f i)) : TotallyRealRoots (∑ i ∈ s, n i) (fun α => ∏ i ∈ s, f i α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact hC.one
  | @insert a s ha ih =>
    have e : (fun α => ∏ i ∈ insert a s, f i α) = fun α => f a α * ∏ i ∈ s, f i α := by
      funext α
      rw [Finset.prod_insert ha]
    rw [e, Finset.sum_insert ha]
    exact hC.mul _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
end Formalism.MainNotions.PlaneGram.CostOK
