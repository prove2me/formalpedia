-- Prove2me | solution 1 for Formalism.CountingSumsFrames.lcomp_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:53.812487+00:00
-- url     : https://prove2.me/submissions/f250bc51-5b0c-4763-bf6a-e532ba9d1edf

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_cons
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_keep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (φ : ι → V →ₗ[K] V) (π : V →ₗ[K] V) (C : Set V) :
    ∀ l : List ι, (∀ j ∈ l, ∀ u ∈ C, φ j u ∈ C) → (∀ j ∈ l, ∀ u ∈ C, π (φ j u) = φ j (π u)) →
      ∀ u ∈ C, π (lcomp φ l u) = lcomp φ l (π u)
  | [], _, _, u, _ => rfl
  | i :: l, hk, hc, u, hu => by
    rw [lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply]
    have hk' : ∀ j ∈ l, ∀ u ∈ C, φ j u ∈ C := fun j hj => hk j (List.mem_cons_of_mem _ hj)
    have hc' : ∀ j ∈ l, ∀ u ∈ C, π (φ j u) = φ j (π u) := fun j hj => hc j (List.mem_cons_of_mem _ hj)
    rw [hc i List.mem_cons_self _ (lcomp_keep φ C l hk' u hu), solution φ π C l hk' hc' u hu]
end Formalism.CountingSumsFrames
