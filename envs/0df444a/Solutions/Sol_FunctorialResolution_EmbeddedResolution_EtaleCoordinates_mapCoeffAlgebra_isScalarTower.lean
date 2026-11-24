-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.mapCoeffAlgebra_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:24.5388+00:00
-- url     : https://prove2.me/submissions/b4455290-36bd-4d19-96e2-783252493d2b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_eq_mvPolynomial_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_eq_sumEval
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_mapCoeffAlgebra_isScalarTower_of_isScalarTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply


attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inr
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
open MvPolynomial
section
variable (k : Type*) [CommRing k] (ι κ : Type*)
end
section
variable (k : Type*) [CommRing k] (ι κ : Type*)
attribute [local instance] sumEvalIterAlgebra
end
section
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S]
attribute [local instance] mapCoeffAlgebra
end
section
universe u v
end
section
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]
attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra
private theorem algebraMap_eq_sumEvalIter (p : MvPolynomial (ι ⊕ κ) k) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k)) p
      = sumEvalIter k ι κ p := rfl
variable (T : Type*) [CommRing T]
end
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

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
theorem _root_.solution [IsScalarTower k (MvPolynomial ι k) S] :
    IsScalarTower (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))
      (MvPolynomial κ S) := by
  have := mapCoeffAlgebra_isScalarTower_of_isScalarTower k ι κ S
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · simp only [algebraMap_eq_sumEval, RingHom.comp_apply, algebraMap_eq_sumEvalIter,
      sumEval, sumEvalIter, MvPolynomial.aeval_C]
    exact IsScalarTower.algebraMap_apply k (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) r
  · rcases v with i | j <;>
      simp [RingHom.comp_apply, algebraMap_eq_sumEval, algebraMap_eq_sumEvalIter,
        sumEval, sumEvalIter, algebraMap_eq_mvPolynomial_map, coord_def]
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
