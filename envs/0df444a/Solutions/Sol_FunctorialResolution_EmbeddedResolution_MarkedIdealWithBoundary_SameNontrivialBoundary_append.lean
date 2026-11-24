-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.SameNontrivialBoundary.append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:54:11.324744+00:00
-- url     : https://prove2.me/submissions/bc8cd764-8761-4a24-9793-5e9af987bc89

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificateMonotone
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedIdealWithBoundary_nontrivialPart_append

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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary
namespace FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary
namespace SameNontrivialBoundary
theorem _root_.solution {X : Scheme.{u}} {L₁ L₁' L₂ L₂' : List X.IdealSheafData}
    (h₁ : SameNontrivialBoundary L₁ L₁') (h₂ : SameNontrivialBoundary L₂ L₂') :
    SameNontrivialBoundary (L₁ ++ L₂) (L₁' ++ L₂') := by
  have e₁ : nontrivialPart L₁ = nontrivialPart L₁' := h₁
  have e₂ : nontrivialPart L₂ = nontrivialPart L₂' := h₂
  show nontrivialPart (L₁ ++ L₂) = nontrivialPart (L₁' ++ L₂')
  rw [nontrivialPart_append, nontrivialPart_append, e₁, e₂]
end SameNontrivialBoundary
end FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary
