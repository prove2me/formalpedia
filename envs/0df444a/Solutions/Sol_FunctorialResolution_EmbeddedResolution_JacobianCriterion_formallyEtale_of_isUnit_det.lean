-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.JacobianCriterion.formallyEtale_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:02.17518+00:00
-- url     : https://prove2.me/submissions/a8a2b26b-c875-404b-aa2d-ef3dc29f27bd

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_formallyEtale_of_basis
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_coordBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.coordBasis_apply

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.JacobianCriterion
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.JacobianCriterion
theorem _root_.solution [Algebra.FormallySmooth k S]
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    Algebra.FormallyEtale (MvPolynomial ι k) S :=
  formallyEtale_of_basis k ι S (coordBasis k ι S b h) (coordBasis_apply k ι S b h)
end FunctorialResolution.EmbeddedResolution.JacobianCriterion
