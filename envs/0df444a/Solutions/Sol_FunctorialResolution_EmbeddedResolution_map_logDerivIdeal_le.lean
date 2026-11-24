-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_logDerivIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:39.228696+00:00
-- url     : https://prove2.me/submissions/6737fe63-13a8-4622-a4d8-20c5c45ec09b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mapToLocalization_mem_tangentDerivations
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_logDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_logDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_le_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.mapToLocalization_algebraMap



set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (M : Submonoid S) [IsLocalization M S'] (P J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') ≤
      logDerivIdeal k (P.map (algebraMap S S')) (J.map (algebraMap S S')) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_logDerivIdeal k _ _ (Ideal.mem_map_of_mem _ hx)
  · intro D hD x hx
    rw [Ideal.mem_comap]
    have h : algebraMap S S' (D x) =
        (D.mapToLocalization (S' := S') M) (algebraMap S S' x) := by
      rw [Derivation.mapToLocalization_algebraMap]
    rw [h]
    exact derivation_apply_mem_logDerivIdeal k _ _ _
      (mapToLocalization_mem_tangentDerivations (S' := S') k M hD)
      (Ideal.mem_map_of_mem _ hx)
end FunctorialResolution.EmbeddedResolution
