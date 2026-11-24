-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:37.916739+00:00
-- url     : https://prove2.me/submissions/fe0f7be4-5cef-4d6a-a906-b05cdd2f9812

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
    (U : ι → Y.Opens) (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) :
    r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ g' =
      r ≫ pullback.snd g' (sigmaOpensDesc Y U) ≫ sigmaOpensDesc Y U := by
  rw [pullback.condition]
end FunctorialResolution.EmbeddedResolution
