-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:08.546191+00:00
-- url     : https://prove2.me/submissions/91bc505c-1b86-4b62-a5d3-3c23cabf0c73

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_BlowupSequenceData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
namespace FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData
theorem _root_.solution (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
  BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i
end FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData
