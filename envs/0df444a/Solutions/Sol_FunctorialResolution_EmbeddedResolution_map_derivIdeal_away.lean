-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_derivIdeal_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:22.337688+00:00
-- url     : https://prove2.me/submissions/24d8ba67-f4bb-493a-b39e-ffd96b08afeb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_derivIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k : Type u} {S : Type v} {S' : Type w}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  map_derivIdeal (Submonoid.powers g) J
end FunctorialResolution.EmbeddedResolution
