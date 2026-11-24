-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.map_logDerivIdeal_ker_le_derivIdeal_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:22.378213+00:00
-- url     : https://prove2.me/submissions/d9b4ba43-6910-463d-9575-67efa565d922

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivationOfSurjective
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealQuotient
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivationOfSurjective_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_tangentDerivations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivationOfSurjective_apply



set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S T : Type*} [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (f : S →ₐ[k] T)
    (hf : Function.Surjective f) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdeal k (RingHom.ker f.toRingHom) J)
      ≤ derivIdeal k (Ideal.map f.toRingHom J) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_derivIdeal k (Ideal.map f.toRingHom J) (Ideal.mem_map_of_mem f.toRingHom hx)
  · intro D hD x hx
    have hD' : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom :=
      (mem_tangentDerivations k (RingHom.ker f.toRingHom) D).mp hD
    have hmem : f x ∈ Ideal.map f.toRingHom J := Ideal.mem_map_of_mem f.toRingHom hx
    have h2 := derivation_apply_mem_derivIdeal k (Ideal.map f.toRingHom J)
      (derivationOfSurjective f hf D hD') hmem
    rw [derivationOfSurjective_apply] at h2
    rw [Ideal.mem_comap]
    exact h2
end FunctorialResolution.EmbeddedResolution
