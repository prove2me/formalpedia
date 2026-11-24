-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_mem_logDerivIdeal_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:18:10.072248+00:00
-- url     : https://prove2.me/submissions/323e99ae-02be-48bf-809c-ce509a3f0fb3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_mem_tangentDerivations_of_ne
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_logDerivIdeal


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
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution {i h : ι} (hih : i ≠ h) (J : Ideal S) {g : S}
    (hg : g ∈ J) :
    partialDeriv k ι S i g ∈ logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J :=
  derivation_apply_mem_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J
    (partialDeriv k ι S i) (partialDeriv_mem_tangentDerivations_of_ne k ι S hih) hg
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
