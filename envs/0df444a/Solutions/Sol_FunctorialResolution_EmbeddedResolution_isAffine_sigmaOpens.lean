-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isAffine_sigmaOpens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:02.675087+00:00
-- url     : https://prove2.me/submissions/904fe94d-1cd1-42ed-88a4-204d76fdcf71

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
theorem _root_.solution (Y : Scheme.{u}) {ι : Type u} [Finite ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) : IsAffine (sigmaOpens Y U) := by
  have : ∀ i, IsAffine (U i).toScheme := fun i => hU i
  exact inferInstanceAs (IsAffine (∐ fun i => (U i).toScheme))
end FunctorialResolution.EmbeddedResolution
