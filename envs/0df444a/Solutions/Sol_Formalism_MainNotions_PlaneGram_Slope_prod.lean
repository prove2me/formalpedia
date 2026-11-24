-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.Slope.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:28.046206+00:00
-- url     : https://prove2.me/submissions/963699ad-11aa-43bd-9f6b-05875448b364

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_prod_nonneg
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
open Formalism.MainNotions.PlaneGram.Slope
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}
namespace Formalism.MainNotions.PlaneGram.Slope
theorem _root_.solution (h1 : TotallyRealRoots 0 (fun _ => 1))
    (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {κ : Type} (s : Finset κ) (f : κ → (σ →₀ ℕ) → K) (hf : ∀ i ∈ s, ∀ α, 0 ≤ v (f i α))
    (sf : ∀ i ∈ s, Slope v TotallyRealRoots c (f i)) : Slope v TotallyRealRoots c (fun α => ∏ i ∈ s, f i α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Slope.one h1
  | @insert a s ha ih =>
    have e : (fun α => ∏ i ∈ insert a s, f i α) = fun α => f a α * ∏ i ∈ s, f i α := by
      funext α
      rw [Finset.prod_insert ha]
    rw [e]
    exact Slope.mul hmul (hf a (Finset.mem_insert_self a s))
      (fun α => v_prod_nonneg _ _ (fun i hi => hf i (Finset.mem_insert_of_mem hi) α))
      (sf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => sf i (Finset.mem_insert_of_mem hi)))
end Formalism.MainNotions.PlaneGram.Slope
