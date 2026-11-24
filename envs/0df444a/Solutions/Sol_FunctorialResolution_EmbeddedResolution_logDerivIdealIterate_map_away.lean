-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealIterate_map_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:51:03.59438+00:00
-- url     : https://prove2.me/submissions/18b7d5b7-f634-47a1-ad6c-7c122b5e256e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_map

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
theorem _root_.solution (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) :=
  logDerivIdealIterate_map k (Submonoid.powers g) hP r J
end FunctorialResolution.EmbeddedResolution
