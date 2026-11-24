-- Prove2me | solution 1 for FunctorialResolution.Blowup.isOpen_connectedComponent_of_noetherianSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:28.304823+00:00
-- url     : https://prove2.me/submissions/79b7a02e-308f-421f-9240-6ff93608fb11

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution (T : Type v) [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] (x : T) : IsOpen (connectedComponent x) := by
  classical
  have hfin : {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}.Finite := by
    refine Set.Finite.subset
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) ?_
    rintro Z ⟨hZ, -⟩
    exact hZ
  have heq : (connectedComponent x)ᶜ
      = ⋃ Z ∈ {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}, Z := by
    apply Set.Subset.antisymm
    · intro y hy
      exact Set.mem_biUnion
        (⟨irreducibleComponent_mem_irreducibleComponents y,
          fun h => hy (h mem_irreducibleComponent)⟩ :
          irreducibleComponent y ∈
            {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x})
        mem_irreducibleComponent
    · intro z hz
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hz
      obtain ⟨Z, ⟨hZ, hZ'⟩, hzZ⟩ := hz
      intro hzc
      have h1 : Z ⊆ connectedComponent z :=
        hZ.1.2.isPreconnected.subset_connectedComponent hzZ
      rw [← connectedComponent_eq hzc] at h1
      exact hZ' h1
  rw [← isClosed_compl_iff, heq]
  exact hfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents _ hZ.1)
end FunctorialResolution.Blowup
