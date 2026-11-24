-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdeal_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:19.798117+00:00
-- url     : https://prove2.me/submissions/a043923c-606e-4e09-a26a-f2219078313c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_logDerivIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_map_le_map_logDerivIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) :=
  le_antisymm (map_logDerivIdeal_le k M P J) (logDerivIdeal_map_le_map_logDerivIdeal k M hP J)
end FunctorialResolution.EmbeddedResolution
