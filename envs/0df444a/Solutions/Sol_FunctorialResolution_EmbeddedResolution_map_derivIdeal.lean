-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_derivIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:03:40.089421+00:00
-- url     : https://prove2.me/submissions/44f0ab3f-5454-4bb0-bed0-5337ed13105e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_derivIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_map_le

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
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  le_antisymm (map_derivIdeal_le M J) (derivIdeal_map_le M J)
end FunctorialResolution.EmbeddedResolution
