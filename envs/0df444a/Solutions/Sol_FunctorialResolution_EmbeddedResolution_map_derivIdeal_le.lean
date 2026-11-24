-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_derivIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:08.539317+00:00
-- url     : https://prove2.me/submissions/3ce21ecc-9007-43ee-9a0c-bb8cd9252d19

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.mapToLocalization_algebraMap



set_option autoImplicit false
universe u v w
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k : Type u} {S : Type v} {S' : Type w}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) ≤
      derivIdeal k (Ideal.map (algebraMap S S') J) := by
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  · intro x hx
    refine Ideal.mem_comap.mpr ?_
    exact le_derivIdeal k _ (Ideal.mem_map_of_mem (algebraMap S S') hx)
  · intro D x hx
    refine Ideal.mem_comap.mpr ?_
    have h := derivation_apply_mem_derivIdeal k (Ideal.map (algebraMap S S') J)
      (D.mapToLocalization (S' := S') M) (Ideal.mem_map_of_mem (algebraMap S S') hx)
    rwa [Derivation.mapToLocalization_algebraMap] at h
end FunctorialResolution.EmbeddedResolution
