-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:23:36.774713+00:00
-- url     : https://prove2.me/submissions/c312d2aa-d2bb-4f87-a553-428de3a0908a

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
theorem _root_.solution {f : Y → X}
    (hf : Topology.IsClosedEmbedding f) {y : Y} {T : Set Y} (h : IsGenericPoint y T) :
    IsGenericPoint (f y) (f '' T) := by
  have hyT : y ∈ T := IsGenericPoint.mem h
  show closure ({f y} : Set X) = f '' T
  apply Set.Subset.antisymm
  · have hcl : IsClosed (f '' T) := by
      rw [← IsGenericPoint.def h]
      exact hf.isClosedMap _ isClosed_closure
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨y, hyT, rfl⟩)
  · have h2 : f '' closure ({y} : Set Y) ⊆ closure (f '' ({y} : Set Y)) :=
      image_closure_subset_closure_image hf.continuous
    rw [Set.image_singleton] at h2
    rw [← IsGenericPoint.def h]
    exact h2
end FunctorialResolution.EmbeddedResolution
