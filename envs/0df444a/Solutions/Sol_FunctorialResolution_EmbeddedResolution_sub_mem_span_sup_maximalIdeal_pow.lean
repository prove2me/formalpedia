-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.sub_mem_span_sup_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:23.325007+00:00
-- url     : https://prove2.me/submissions/cc836eae-bf5f-4faf-b47f-0c8fa1ff24aa

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_truncatedSeries_sub_mem_maximalIdeal_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeries_sub_mem_span_singleton


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (N : ℕ) (hN : 1 ≤ N) (f : R) :
    φ f - φ' f ∈ Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N := by
  have h1 : TaylorExpansion.truncatedSeries φ D β N f - φ f ∈ Ideal.span ({β} : Set B) :=
    TaylorExpansion.truncatedSeries_sub_mem_span_singleton φ D β N hN f
  have h2 : TaylorExpansion.truncatedSeries φ D β N f - φ' f ∈ maximalIdeal B ^ N :=
    truncatedSeries_sub_mem_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f
  have hEq : φ f - φ' f
      = (TaylorExpansion.truncatedSeries φ D β N f - φ' f) - (TaylorExpansion.truncatedSeries φ D β N f - φ f) := by
    ring
  rw [hEq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right h2) (Submodule.mem_sup_left h1)
end FunctorialResolution.EmbeddedResolution
