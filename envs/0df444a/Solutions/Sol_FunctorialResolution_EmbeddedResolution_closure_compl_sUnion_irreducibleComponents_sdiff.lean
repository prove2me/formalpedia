-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.closure_compl_sUnion_irreducibleComponents_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:39.562529+00:00
-- url     : https://prove2.me/submissions/3537f129-d3e8-422c-b12c-b77827cfc739

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_VanishingIdealOfComponents
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_compl_sUnion_irreducibleComponents_sdiff_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*} [TopologicalSpace α]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [NoetherianSpace α]
    {S : Set (Set α)} (hS : S ⊆ irreducibleComponents α) :
    closure ((⋃₀ (irreducibleComponents α \ S))ᶜ) = ⋃₀ S := by
  have hZcl : IsClosed (⋃₀ (irreducibleComponents α \ S)) :=
    isClosed_sUnion_irreducibleComponents Set.sdiff_subset
  apply Set.Subset.antisymm
  · exact closure_minimal (compl_sUnion_irreducibleComponents_sdiff_subset S)
      (isClosed_sUnion_irreducibleComponents hS)
  · rintro x ⟨C, hCS, hxC⟩
    have hCcomp : C ∈ irreducibleComponents α := hS hCS
    have hCirr : IsIrreducible C := hCcomp.1
    have hnot : ¬ C ⊆ ⋃₀ (irreducibleComponents α \ S) := by
      intro hsub
      have hfin : (irreducibleComponents α \ S).Finite :=
        Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents)
          Set.sdiff_subset
      obtain ⟨D, hD, hCsubD⟩ := isIrreducible_iff_sUnion_isClosed.mp hCirr hfin.toFinset
        (fun z hz => isClosed_of_mem_irreducibleComponents z (hfin.mem_toFinset.mp hz).1)
        (by rwa [hfin.coe_toFinset])
      have hD' : D ∈ irreducibleComponents α \ S := hfin.mem_toFinset.mp hD
      have hDsubC : D ⊆ C := hCcomp.2 hD'.1.1 hCsubD
      exact hD'.2 (by rw [Set.Subset.antisymm hDsubC hCsubD]; exact hCS)
    obtain ⟨y, hyC, hyZ⟩ := Set.not_subset.mp hnot
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨z, hz, hzo, hzZ⟩ := hCirr.2 o (⋃₀ (irreducibleComponents α \ S))ᶜ ho
      hZcl.isOpen_compl ⟨x, hxC, hxo⟩ ⟨y, hyC, hyZ⟩
    exact ⟨z, hzo, hzZ⟩
end FunctorialResolution.EmbeddedResolution
