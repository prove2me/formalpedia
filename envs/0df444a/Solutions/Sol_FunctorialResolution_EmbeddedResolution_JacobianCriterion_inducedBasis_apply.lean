-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:38.810992+00:00
-- url     : https://prove2.me/submissions/bd97fcff-b299-4727-b344-7b5f60f3c499

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
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] [Algebra k S]
variable (S' : Type*) [CommRing S'] [Algebra k S'] [Algebra S S'] [IsScalarTower k S S']
variable [Algebra.FormallyEtale S S']
namespace FunctorialResolution.EmbeddedResolution.JacobianCriterion
theorem _root_.solution (b : Module.Basis ι S (KaehlerDifferential k S)) (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.map k k S S' (b i) :=
  Module.Basis.mk_apply (linearIndependent_kaehlerMap_basis k ι S S' b)
    (top_le_span_kaehlerMap_basis k ι S S' b) i
end FunctorialResolution.EmbeddedResolution.JacobianCriterion
