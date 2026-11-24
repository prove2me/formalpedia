-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isAffine_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:52.341801+00:00
-- url     : https://prove2.me/submissions/6bf98e00-c517-4793-a4af-e48eaa15eda2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_FieldExtensionEtaleCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
noncomputable section
variable {k : Type u} [Field k] {X W : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (p : W ⟶ Spec (CommRingCat.of k)) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange p K) := by
  have : IsAffineHom (baseChangeProjection p K) :=
    morphismProperty_of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
      inferInstance
  exact isAffine_of_isAffineHom (f := baseChangeProjection p K)
end FunctorialResolution.EmbeddedResolution
