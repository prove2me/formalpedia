-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isGenericPoint_preimage_of_isInducing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:48.386872+00:00
-- url     : https://prove2.me/submissions/ce628ee2-563c-473c-8387-2c306de1dcf9

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
theorem _root_.solution {f : Y → X} (hf : Topology.IsInducing f)
    {ξ : X} {T : Set X} (h : IsGenericPoint ξ T) {y : Y} (hy : f y = ξ) :
    IsGenericPoint y (f ⁻¹' T) := by
  have h2 : closure ({y} : Set Y) = f ⁻¹' closure (f '' ({y} : Set Y)) :=
    hf.closure_eq_preimage_closure_image _
  rw [Set.image_singleton, hy, IsGenericPoint.def h] at h2
  exact h2
end FunctorialResolution.EmbeddedResolution
