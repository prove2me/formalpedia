-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.surjective_comp_fst_pullback_sigmaOpensDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:51:32.914878+00:00
-- url     : https://prove2.me/submissions/c233f40c-6590-4302-9822-118f8285081b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpensPullback
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_surjective_sigmaOpensDesc


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
    (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective (r ≫ pullback.fst g' (sigmaOpensDesc Y U)) := by
  have := surjective_sigmaOpensDesc Y U hU
  have : Surjective (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance
end FunctorialResolution.EmbeddedResolution
