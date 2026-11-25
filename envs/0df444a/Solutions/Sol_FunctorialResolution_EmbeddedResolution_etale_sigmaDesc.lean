-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.etale_sigmaDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:11.158975+00:00
-- url     : https://prove2.me/submissions/fd250b7e-bd3c-4336-94ad-5744ff16da5f

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
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Etale (f i)) : Etale (Sigma.desc f) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc hf
end FunctorialResolution.EmbeddedResolution
