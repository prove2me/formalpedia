-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.structureMorphism_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:46.054942+00:00
-- url     : https://prove2.me/submissions/4b8fabf8-615b-4263-89bf-1724a318e5cc

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
    s.structureMorphism i = s.toSequenceOfBlowups.projectionToBase i ≫ p := rfl
end FunctorialResolution.EmbeddedResolution.IdealBlowupSequence
