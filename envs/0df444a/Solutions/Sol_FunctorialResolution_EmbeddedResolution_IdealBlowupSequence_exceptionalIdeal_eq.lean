-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.exceptionalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:36.559081+00:00
-- url     : https://prove2.me/submissions/e944e2ee-da58-44d6-8764-42a236d01546

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
theorem _root_.solution (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.exceptionalIdeal i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := rfl
end FunctorialResolution.EmbeddedResolution.IdealBlowupSequence
