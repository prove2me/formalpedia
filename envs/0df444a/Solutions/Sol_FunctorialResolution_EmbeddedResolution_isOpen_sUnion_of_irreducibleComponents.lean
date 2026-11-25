-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:23:55.911042+00:00
-- url     : https://prove2.me/submissions/9e1cefe1-655a-4e11-8cb0-204ce28e8918

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {Z : Type*} [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Z] (C : Set (Set Z))
    (hdisj : ∀ S ∈ C, ∀ W ∈ irreducibleComponents Z, W ∉ C → Disjoint S W) :
    IsOpen (⋃₀ C) := by
  have hcomp : (irreducibleComponents Z).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hfin : (irreducibleComponents Z \ C).Finite := hcomp.subset Set.sdiff_subset
  have hclosed : IsClosed (⋃₀ (irreducibleComponents Z \ C)) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun i hi => isClosed_of_mem_irreducibleComponents i hi.1
  have heq : ⋃₀ C = (⋃₀ (irreducibleComponents Z \ C))ᶜ := by
    apply Set.Subset.antisymm
    · rintro x ⟨S, hSmem, hxS⟩
      have hx : x ∉ ⋃₀ (irreducibleComponents Z \ C) := by
        rintro ⟨W, ⟨hW, hWC⟩, hxW⟩
        exact Set.disjoint_left.mp (hdisj S hSmem W hW hWC) hxS hxW
      exact hx
    · intro x hx
      rw [Set.mem_compl_iff] at hx
      by_cases hmem : irreducibleComponent x ∈ C
      · exact Set.mem_sUnion_of_mem mem_irreducibleComponent hmem
      · exact absurd (Set.mem_sUnion_of_mem mem_irreducibleComponent
          (Set.mem_sdiff_of_mem (irreducibleComponent_mem_irreducibleComponents x) hmem)) hx
  rw [heq]
  exact hclosed.isOpen_compl
end FunctorialResolution.EmbeddedResolution
