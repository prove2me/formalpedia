-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cost_choose_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:40:54.351083+00:00
-- url     : https://prove2.me/submissions/0ca99f46-40b2-4880-bb90-c4243e3e87d7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_CostOK_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_choose_affine

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
theorem _root_.solution (hC : CostOK TotallyRealRoots) (u : (σ →₀ ℕ) → ℕ)
    (hu : ∀ k, TotallyRealRoots k (fun α => ((u α).choose k : K))) (ρ P m : ℕ) :
    TotallyRealRoots m (fun α => ((ρ + P * u α).choose m : K)) := by
  obtain ⟨z, hz⟩ := choose_affine ρ P m
  have e : (fun α => (((ρ + P * u α).choose m : ℕ) : K)) =
      fun α => ∑ i ∈ Finset.range (m + 1), (z i : K) * ((u α).choose i : K) := by
    funext α
    rw [hz (u α)]
    push_cast
    rfl
  rw [e]
  exact hC.sum (Finset.range (m + 1)) m (fun i α => (z i : K) * ((u α).choose i : K))
    (fun i hi => hC.smul m (z i : K) _
      (hC.mono i m _ (by have := Finset.mem_range.mp hi; omega) (hu i)))
end Formalism.MainNotions.PlaneGram
