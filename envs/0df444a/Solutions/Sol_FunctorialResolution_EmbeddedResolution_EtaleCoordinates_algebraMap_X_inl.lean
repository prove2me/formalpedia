-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:47.683318+00:00
-- url     : https://prove2.me/submissions/3d39c327-8f51-4437-bf8a-2f14288b834e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_eq_sumEval
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply



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
theorem _root_.solution (i : ι) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) (X (Sum.inl i))
      = C (coord k ι S i) := by
  simp [algebraMap_eq_sumEval, sumEval]
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
