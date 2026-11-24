-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.formallyEtale_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:14:34.901792+00:00
-- url     : https://prove2.me/submissions/4ef29287-4d9f-486d-9247-c523f284139d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_formallyEtale_mvPolynomial_sum

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
variable (T : Type*) [CommRing T]
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra (MvPolynomial κ S) T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) T]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial κ S) T] :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T := by
  have := formallyEtale_mvPolynomial_sum k ι κ S
  exact Algebra.FormallyEtale.comp (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) T
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
