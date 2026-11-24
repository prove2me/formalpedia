-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.JacobianCriterion.tensorKaehlerBasis_mapBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:48.097809+00:00
-- url     : https://prove2.me/submissions/380d1c08-96cf-48d4-a239-4edd6c8883af

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.JacobianCriterion
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.JacobianCriterion
theorem _root_.solution (i : ι) :
    KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S (tensorKaehlerBasis k ι S i) =
      KaehlerDifferential.D k S (coord k ι S i) := by
  have h : tensorKaehlerBasis k ι S i =
      (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) (MvPolynomial.X i)) :=
    Module.Basis.mk_apply (linearIndependent_one_tmul_D_X k ι S) (top_le_span_one_tmul_D_X k ι S) i
  have h2 : coord k ι S i = algebraMap (MvPolynomial ι k) S (MvPolynomial.X i) := rfl
  rw [h, KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, h2]
end FunctorialResolution.EmbeddedResolution.JacobianCriterion
