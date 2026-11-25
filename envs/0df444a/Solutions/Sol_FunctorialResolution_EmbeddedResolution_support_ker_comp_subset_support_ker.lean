-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.support_ker_comp_subset_support_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:24:14.522417+00:00
-- url     : https://prove2.me/submissions/2ad0ba6c-6633-48f8-a416-e8913b4478d3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {T S Y : Scheme}
    (g : T ⟶ S) (f : S ⟶ Y) :
    ((g ≫ f).ker.support : Set Y) ⊆ (f.ker.support : Set Y) := by
  intro x hx
  exact Scheme.IdealSheafData.support_antitone (Scheme.Hom.le_ker_comp g f) hx
end FunctorialResolution.EmbeddedResolution
