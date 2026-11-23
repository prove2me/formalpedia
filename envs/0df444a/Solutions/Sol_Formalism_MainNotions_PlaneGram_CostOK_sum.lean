-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.CostOK.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:04.258487+00:00
-- url     : https://prove2.me/submissions/fd28eea2-a0d3-4073-a5a3-47477ef203e3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_CostOK_zero

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
theorem _root_.solution (hC : CostOK TotallyRealRoots) {κ : Type} (s : Finset κ) (n : ℕ) (f : κ → (σ →₀ ℕ) → K)
    (h : ∀ i ∈ s, TotallyRealRoots n (f i)) : TotallyRealRoots n (fun α => ∑ i ∈ s, f i α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact hC.zero n
  | @insert a s ha ih =>
    have e : (fun α => ∑ i ∈ insert a s, f i α) = fun α => f a α + ∑ i ∈ s, f i α := by
      funext α
      rw [Finset.sum_insert ha]
    rw [e]
    exact hC.add n _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
end Formalism.MainNotions.PlaneGram.CostOK
