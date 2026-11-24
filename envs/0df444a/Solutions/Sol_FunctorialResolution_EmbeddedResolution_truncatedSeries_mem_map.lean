-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.truncatedSeries_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:19.98098+00:00
-- url     : https://prove2.me/submissions/198e46d1-f8f3-497f-892c-e867be5cfd5f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra A R]
    [Algebra ℚ B] (φ : R →+* B) (D : Derivation A R R) (b : R) (J : Ideal R)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J)
    (N : ℕ) (g : R) (hg : g ∈ J) :
    TaylorExpansion.truncatedSeries φ D (φ b) N g ∈ Ideal.map φ J := by
  rw [TaylorExpansion.truncatedSeries_apply]
  refine Ideal.sum_mem _ fun j _ => ?_
  have h : φ (b ^ j * (⇑D)^[j] g) ∈ Ideal.map φ J :=
    Ideal.mem_map_of_mem φ (hstab j g hg)
  rw [map_mul, map_pow] at h
  have h2 := Ideal.mul_mem_left (Ideal.map φ J) (algebraMap ℚ B ((j.factorial : ℚ)⁻¹)) h
  have h3 : algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * φ ((⇑D)^[j] g) * φ b ^ j
      = algebraMap ℚ B ((j.factorial : ℚ)⁻¹) * (φ b ^ j * φ ((⇑D)^[j] g)) := by
    ring
  rw [h3]
  exact h2
end FunctorialResolution.EmbeddedResolution
