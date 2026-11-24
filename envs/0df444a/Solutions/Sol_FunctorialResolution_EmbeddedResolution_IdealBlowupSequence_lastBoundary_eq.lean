-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.lastBoundary_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:40.849103+00:00
-- url     : https://prove2.me/submissions/60e24c9e-c4f7-4896-90df-b1c39d5a8658

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence

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
open FunctorialResolution.EmbeddedResolution.IdealBlowupSequence
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}
namespace FunctorialResolution.EmbeddedResolution.IdealBlowupSequence
theorem _root_.solution (s : IdealBlowupSequence p I E) :
    s.lastBoundary = s.boundary s.toSequenceOfBlowups.length := rfl
end FunctorialResolution.EmbeddedResolution.IdealBlowupSequence
