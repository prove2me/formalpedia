-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsMaxOrderReduction.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:16:52.848213+00:00
-- url     : https://prove2.me/submissions/e610f51d-d2b0-4d67-9ec0-cd3753f089a6

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
namespace FunctorialResolution.EmbeddedResolution
namespace IsMaxOrderReduction
theorem _root_.solution {P : ℕ → Prop} {A B : PrincipalizationAssignment.{u}}
    (hs : IsMaxOrderReduction P A B) (Q : ℕ → Prop) (hQP : ∀ n, Q n → P n) :
    IsMaxOrderReduction Q A B := by
  constructor
  · intro T hV hQ
    exact hs.cert T hV (hQP _ hQ)
  · intro T hV hQ
    exact hs.orderRed_equiv T hV (hQP _ hQ)
  · intro T hV hQ L _ _ f E' hBE hV' hQ'
    exact hs.base_change T hV (hQP _ hQ) L f E' hBE hV' (hQP _ hQ')
  · intro T hV hQ L _ _ f E' hBE hV' hQ'
    exact hs.base_change_strict T hV (hQP _ hQ) L f E' hBE hV' (hQP _ hQ')
  · intro T hV hQ
    exact hs.center_nonempty T hV (hQP _ hQ)
  · intro T hV hQ
    exact hs.resolves T hV (hQP _ hQ)
  · intro T hV hQ Y q h _ hq E' hBE hV' hQ'
    exact hs.smooth_pullback T hV (hQP _ hQ) Y q h hq E' hBE hV' (hQP _ hQ')
  · intro T hV hQ Y q h _ _ hq E' hBE hV' hQ'
    exact hs.smooth_pullback_strict T hV (hQP _ hQ) Y q h hq E' hBE hV' (hQP _ hQ')
  · intro T hV hQ
    exact hs.trivial_of_coSupport_empty T hV (hQP _ hQ)
end IsMaxOrderReduction
end FunctorialResolution.EmbeddedResolution
