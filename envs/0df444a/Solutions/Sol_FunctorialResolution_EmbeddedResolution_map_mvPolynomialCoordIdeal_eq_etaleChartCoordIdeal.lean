-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_mvPolynomialCoordIdeal_eq_etaleChartCoordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:00:32.981581+00:00
-- url     : https://prove2.me/submissions/590ed2fe-7183-4e91-ba23-79c41a6e2367

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoordIdeal_eq_span_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] (J : Finset (Fin m)) :
    Ideal.map (algebraMap (CoordPolynomialRing k m) S) (mvPolynomialCoordIdeal k m J) =
      etaleChartCoordIdeal k m S J := by
  rw [etaleChartCoordIdeal_eq_span_image, mvPolynomialCoordIdeal_eq_span, Ideal.map_span, Set.image_image]
  rfl
end FunctorialResolution.EmbeddedResolution
