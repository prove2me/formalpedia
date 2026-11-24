-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isIrreducible_inter_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:10.442037+00:00
-- url     : https://prove2.me/submissions/99671434-6108-4c97-bbc7-6ef6f6e58781

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
theorem _root_.solution {S U : Set X} (hS : IsIrreducible S) (hU : IsOpen U)
    (hne : (S ∩ U).Nonempty) : IsIrreducible (S ∩ U) := by
  refine ⟨hne, ?_⟩
  rintro u v hu hv ⟨a, ⟨haS, haU⟩, hau⟩ ⟨b, ⟨hbS, hbU⟩, hbv⟩
  obtain ⟨c, hcS, hc⟩ := hS.2 (U ∩ u) (U ∩ v) (hU.inter hu) (hU.inter hv)
    ⟨a, haS, haU, hau⟩ ⟨b, hbS, hbU, hbv⟩
  exact ⟨c, ⟨hcS, hc.1.1⟩, hc.1.2, hc.2.2⟩
end FunctorialResolution.EmbeddedResolution
