-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.JacobianCriterion.coordBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:37.749401+00:00
-- url     : https://prove2.me/submissions/4459e973-968f-4303-818c-1ac756d6cfa5

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
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
omit [IsScalarTower k (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.JacobianCriterion
theorem _root_.solution (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) (i : ι) :
    coordBasis k ι S b h i = KaehlerDifferential.D k S (coord k ι S i) :=
  Module.Basis.mk_apply (linearIndependent_D_coord_of_isUnit_det k ι S b h) (top_le_span_D_coord_of_isUnit_det k ι S b h) i
end FunctorialResolution.EmbeddedResolution.JacobianCriterion
