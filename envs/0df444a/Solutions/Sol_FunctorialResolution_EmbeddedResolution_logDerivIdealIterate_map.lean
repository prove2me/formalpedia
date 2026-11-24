-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealIterate_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:35:57.40875+00:00
-- url     : https://prove2.me/submissions/ea846dcc-85c8-4259-8c8f-c94402d828d3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_zero


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
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map (algebraMap S S')) r (J.map (algebraMap S S')) := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ, logDerivIdeal_map k M hP, ih]
end FunctorialResolution.EmbeddedResolution
