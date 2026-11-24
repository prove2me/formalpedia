-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.closure_inter_open_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:40.786307+00:00
-- url     : https://prove2.me/submissions/17b8a082-2f60-4348-90e2-4acc068df261

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
theorem _root_.solution {S U : Set X} (hS : IsClosed S) (hirr : IsIrreducible S)
    (hU : IsOpen U) (hne : (S ∩ U).Nonempty) : closure (S ∩ U) = S := by
  apply Set.Subset.antisymm
  · exact hS.closure_subset_iff.mpr Set.inter_subset_left
  · intro x hx
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨c, hcS, hc⟩ := hirr.2 o U ho hU ⟨x, hx, hxo⟩ hne
    exact ⟨c, hc.1, hcS, hc.2⟩
end FunctorialResolution.EmbeddedResolution
