-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:03.276269+00:00
-- url     : https://prove2.me/submissions/e9497326-255d-41d9-b7a3-e8a0a77c44ec

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) :
    InStrictNormalCrossingPosition p E ↔
      (∀ D ∈ E, IsSmoothDivisor p D) ∧ ∀ x : X, InStrictNormalCrossingPositionAt p E x :=
  Iff.rfl
end FunctorialResolution.EmbeddedResolution
