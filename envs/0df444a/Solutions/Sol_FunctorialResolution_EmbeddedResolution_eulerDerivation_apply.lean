-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.eulerDerivation_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:00.967902+00:00
-- url     : https://prove2.me/submissions/8c234044-5311-46af-9a8f-af6d45cf78c5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open IsLocalRing
private theorem sum_smul_derivation_apply (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} (s : Finset ι) (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    (∑ i ∈ s, x i • D i) a = ∑ i ∈ s, x i * D i a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply,
        Derivation.smul_apply, smul_eq_mul, ih]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    eulerDerivation k x D a = ∑ i, x i * D i a := by
  show (∑ i, x i • D i) a = ∑ i, x i * D i a
  exact sum_smul_derivation_apply k Finset.univ x D a
end FunctorialResolution.EmbeddedResolution
