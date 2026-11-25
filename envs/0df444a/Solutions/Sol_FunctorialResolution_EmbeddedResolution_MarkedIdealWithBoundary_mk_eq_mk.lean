-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.mk_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:21:16.345601+00:00
-- url     : https://prove2.me/submissions/ae0c172c-5832-4338-b556-f3b35c15dc8d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups

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
attribute [instance] MarkedIdealWithBoundary.instField
namespace FunctorialResolution.EmbeddedResolution
namespace MarkedIdealWithBoundary
theorem _root_.solution {k : Type u} [instk : Field k] (X : Scheme.{u}) (m : ℕ)
    {p p' : X ⟶ Spec (CommRingCat.of k)} {I I' : X.IdealSheafData}
    {E E' : List X.IdealSheafData} (hp : p = p') (hI : I = I') (hE : E = E') :
    @MarkedIdealWithBoundary.mk k instk X p I m E = @MarkedIdealWithBoundary.mk k instk X p' I' m E' := by
  subst hp
  subst hI
  subst hE
  rfl
end MarkedIdealWithBoundary
end FunctorialResolution.EmbeddedResolution
