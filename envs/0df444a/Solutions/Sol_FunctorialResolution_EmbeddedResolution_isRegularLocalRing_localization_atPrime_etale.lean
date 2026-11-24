-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRegularLocalRing_localization_atPrime_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:11.069831+00:00
-- url     : https://prove2.me/submissions/44a5c9f4-8b10-4cb5-9692-97f4e416e257

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_isLocalization_etale

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
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  isRegularLocalRing_of_isLocalization_etale k m S q (Localization.AtPrime q)
end FunctorialResolution.EmbeddedResolution
