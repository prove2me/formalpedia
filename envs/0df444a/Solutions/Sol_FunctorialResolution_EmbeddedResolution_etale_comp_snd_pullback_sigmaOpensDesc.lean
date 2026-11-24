-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.etale_comp_snd_pullback_sigmaOpensDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:35.369437+00:00
-- url     : https://prove2.me/submissions/17335393-25dc-41dc-8f71-547651378077

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
theorem _root_.solution (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [Etale g'] (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale (r ≫ pullback.snd g' (sigmaOpensDesc Y U)) := by
  have : Etale (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance
end FunctorialResolution.EmbeddedResolution
