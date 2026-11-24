-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.sub_mem_iInf_span_sup_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:38:18.37871+00:00
-- url     : https://prove2.me/submissions/aa9ef3f5-bce7-4788-9c06-ea341b57e563

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sub_mem_span_sup_maximalIdeal_pow

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
    (f : R) :
    φ f - φ' f ∈ ⨅ N : ℕ, (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N) := by
  refine Submodule.mem_iInf _ |>.2 ?_
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ 0) = ⊤ := by
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
    rw [h0]
    exact Submodule.mem_top
  · exact sub_mem_span_sup_maximalIdeal_pow P φ φ' D β hcong hβ hrep N hN f
end FunctorialResolution.EmbeddedResolution
