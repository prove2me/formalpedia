-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdealIterate_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:31:19.117645+00:00
-- url     : https://prove2.me/submissions/c2f9e009-ba0e-4a84-bb38-7951e1f3c0a6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (h : ι) (J : Ideal S) :
    partialDerivIdealIterate k ι S h 1 J = partialDerivIdeal k ι S h J := rfl
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
