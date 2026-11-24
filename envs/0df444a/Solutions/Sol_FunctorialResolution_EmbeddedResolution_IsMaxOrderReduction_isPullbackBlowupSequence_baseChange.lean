-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsMaxOrderReduction.isPullbackBlowupSequence_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:34:26.976791+00:00
-- url     : https://prove2.me/submissions/e8f22758-867c-401d-841d-c3f91be81702

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedIdealWithBoundary_SameNontrivialBoundary_refl

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
    (hs : IsMaxOrderReduction P A B) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
    (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
    (hV' : (T.baseChange L f).IsAdmissible) (hP' : P (T.baseChange L f).krullDimSucc) :
    IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (A (T.baseChange L f)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.base_change T hV hP L f (T.baseChange L f).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'
end IsMaxOrderReduction
end FunctorialResolution.EmbeddedResolution
