-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:51.022008+00:00
-- url     : https://prove2.me/submissions/bc091bd9-c315-41db-9a21-0185170fec41

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.JacobianCriterion
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] [Algebra k S]
variable (S' : Type*) [CommRing S'] [Algebra k S'] [Algebra S S'] [IsScalarTower k S S']
variable [Algebra.FormallyEtale S S']
namespace FunctorialResolution.EmbeddedResolution.JacobianCriterion
theorem _root_.solution (b : Module.Basis ι S (KaehlerDifferential k S)) (x : ι → S)
    (hx : ∀ i : ι, b i = KaehlerDifferential.D k S (x i)) (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.D k S' (algebraMap S S' (x i)) := by
  rw [inducedBasis_apply, hx i, KaehlerDifferential.map_D]
end FunctorialResolution.EmbeddedResolution.JacobianCriterion
