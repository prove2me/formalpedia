-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_connectedComponent_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:09.208518+00:00
-- url     : https://prove2.me/submissions/0ed6109a-258a-410d-b717-c4b9a883281e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SubschemeMapFlatness

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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {α : Type*} [TopologicalSpace α] {x y z : α}
    (hy : y ∈ connectedComponent x) (h : y ⤳ z) : z ∈ connectedComponent x := by
  have hzy : z ∈ closure ({y} : Set α) := specializes_iff_mem_closure.mp h
  have hpc : _root_.IsPreconnected (closure ({y} : Set α)) :=
    (isPreconnected_singleton : _root_.IsPreconnected ({y} : Set α)).closure
  have hsub : closure ({y} : Set α) ⊆ connectedComponent y :=
    hpc.subset_connectedComponent (subset_closure (Set.mem_singleton y))
  have hz : z ∈ connectedComponent y := hsub hzy
  rwa [← connectedComponent_eq hy] at hz
end FunctorialResolution.EmbeddedResolution
