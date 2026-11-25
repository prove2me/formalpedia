-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.hasStrictNormalCrossingsWith_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:41.957435+00:00
-- url     : https://prove2.me/submissions/733ca9e1-2f44-4427-b60f-5c48aeada83d

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
theorem _root_.solution (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    HasStrictNormalCrossingsWith (s.structureMorphism i) (s.toSequenceOfBlowups.center i) (s.boundary i) :=
  s.center_snc i h
end FunctorialResolution.EmbeddedResolution.IdealBlowupSequence
