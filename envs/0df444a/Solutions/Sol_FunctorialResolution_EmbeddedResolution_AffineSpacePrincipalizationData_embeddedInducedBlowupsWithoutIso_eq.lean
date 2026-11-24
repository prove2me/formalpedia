-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.embeddedInducedBlowupsWithoutIso_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:45.032398+00:00
-- url     : https://prove2.me/submissions/bbc8cc6e-6960-42a4-9143-f911f44bbf18

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_embeddedInducedBlowups_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
namespace FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
theorem _root_.solution (S : AffineSpacePrincipalizationData k Y pY) (h : S.TransitionsAreBlowups) :
    S.toEmbeddedBlowupSequence.inducedBlowupsWithoutIso ((toEmbeddedBlowupSequence_transitionsAreBlowups_iff S).mpr h) = S.blowupSequenceWithoutIsos h := by
  show (S.toEmbeddedBlowupSequence.inducedBlowups ((toEmbeddedBlowupSequence_transitionsAreBlowups_iff S).mpr h)).withoutIsoBlowups
      = (S.blowupSequence h).withoutIsoBlowups
  exact congrArg SequenceOfBlowups.withoutIsoBlowups (embeddedInducedBlowups_eq S h)
end FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
