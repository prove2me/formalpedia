-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.smooth_sigmaDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:11.898979+00:00
-- url     : https://prove2.me/submissions/1bf87da5-da0b-40b5-bf86-807677030c2e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens

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
theorem _root_.solution {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Smooth (f i)) : Smooth (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc hf
end FunctorialResolution.EmbeddedResolution
