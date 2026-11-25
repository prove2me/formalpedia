-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.closure_image_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:19.816719+00:00
-- url     : https://prove2.me/submissions/9d096bee-6452-436c-bdab-32b43c06718f

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
theorem _root_.solution {f : X → Y} (hcont : Continuous f) {S : Set X} {ξ : X}
    (hξ : IsGenericPoint ξ S) : closure (f '' S) = closure ({f ξ} : Set Y) := by
  refine Set.Subset.antisymm ?_ ?_
  · refine closure_minimal ?_ isClosed_closure
    have hsub := image_closure_subset_closure_image (f := f) (s := ({ξ} : Set X)) hcont
    rw [Set.image_singleton] at hsub
    rw [← hξ]
    exact hsub
  · refine closure_mono ?_
    refine Set.singleton_subset_iff.2 ⟨ξ, ?_, rfl⟩
    rw [← hξ]
    exact subset_closure rfl
end FunctorialResolution.EmbeddedResolution
