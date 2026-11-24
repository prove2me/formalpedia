-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.surjective_comp_snd_pullback_sigmaOpensDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:55.497315+00:00
-- url     : https://prove2.me/submissions/ba54352c-61f9-4097-ae8b-dc3ee0af4692

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpensPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Y : Scheme.{u}) {ι : Type u}
    (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [Surjective g'] (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective (r ≫ pullback.snd g' (sigmaOpensDesc Y U)) := by
  have : Surjective (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance
end FunctorialResolution.EmbeddedResolution
