-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isClosed_sUnion_of_subset_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:09.798342+00:00
-- url     : https://prove2.me/submissions/66c963e6-277c-46ff-9b01-d1ab0bdd24a3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_IrreducibleComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open Set TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsClosed (⋃₀ 𝒜) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents ..
  have hsub : 𝒜 ⊆ irreducibleComponents X := fun C hC => h𝒜 C hC
  rw [Set.sUnion_eq_biUnion]
  exact (hfin.subset hsub).isClosed_biUnion
    (fun C hC => isClosed_of_mem_irreducibleComponents _ (h𝒜 C hC))
end FunctorialResolution.EmbeddedResolution
