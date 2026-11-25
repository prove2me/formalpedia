-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_subset_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:24:01.352842+00:00
-- url     : https://prove2.me/submissions/7ebe6600-d6ea-4d1b-b660-5c7fd784f713

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_IrreducibleComponents
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isClosed_sUnion_of_subset_irreducibleComponents

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
    [NoetherianSpace X]
    (hsep : ∀ C₁ ∈ irreducibleComponents X, ∀ C₂ ∈ irreducibleComponents X,
      (C₁ ∩ C₂).Nonempty → C₁ = C₂)
    {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsOpen (⋃₀ 𝒜) := by
  have key : (⋃₀ 𝒜)ᶜ = ⋃₀ (irreducibleComponents X \ 𝒜) := by
    apply Set.Subset.antisymm
    · intro y hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩,
        mem_irreducibleComponent ..⟩
      intro hmem
      exact hy ⟨irreducibleComponent y, hmem, mem_irreducibleComponent ..⟩
    · intro y hyc
      obtain ⟨C, ⟨hC, hCA⟩, hyC⟩ := hyc
      show y ∉ ⋃₀ 𝒜
      intro hy
      obtain ⟨D, hD, hyD⟩ := hy
      have heq : C = D := hsep C hC D (h𝒜 D hD) ⟨y, hyC, hyD⟩
      rw [heq] at hCA
      exact hCA hD
  rw [← isClosed_compl_iff, key]
  exact isClosed_sUnion_of_subset_irreducibleComponents (fun C hC => hC.1)
end FunctorialResolution.EmbeddedResolution
