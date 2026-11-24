-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:34:13.673945+00:00
-- url     : https://prove2.me/submissions/552ef6ae-f73c-4d73-b8ba-ac7f8fe2b881

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
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.Surjective h] (hq : h ≫ T.structMap = q)
    (hV' : (T.pullbackAlong Y q h).IsAdmissible) (hP' : P (T.pullbackAlong Y q h).krullDimSucc) :
    IsStrictPullbackBlowupSeq h (A (T.pullbackAlong Y q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.smooth_pullback_strict T hV hP Y q h hq (T.pullbackAlong Y q h).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'
end IsMaxOrderReduction
end FunctorialResolution.EmbeddedResolution
