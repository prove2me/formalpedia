-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.sumEvalAlgebra_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:37.034377+00:00
-- url     : https://prove2.me/submissions/54986617-43ba-4f3c-9c63-b650b3df9558

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension

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
open MvPolynomial
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]
attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution :
    IsScalarTower k (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) :=
  IsScalarTower.of_algebraMap_eq fun x => ((sumEval k ι κ S).commutes x).symm
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
