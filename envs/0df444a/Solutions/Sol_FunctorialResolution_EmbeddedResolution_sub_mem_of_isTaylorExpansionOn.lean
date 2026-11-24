-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.sub_mem_of_isTaylorExpansionOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:09:33.221875+00:00
-- url     : https://prove2.me/submissions/213e5b0e-d67d-4962-89a6-9b7aa1f05868

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sub_mem_span_singleton_of_isTaylorExpansionOn

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
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (I : Ideal B) (hI : β ∈ I) (f : R) :
    φ f - φ' f ∈ I := by
  have hmem : φ f - φ' f ∈ Ideal.span ({β} : Set B) :=
    sub_mem_span_singleton_of_isTaylorExpansionOn P φ φ' D β hcong hβ hrep f
  have hle : Ideal.span ({β} : Set B) ≤ I :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hI)
  exact hle hmem
end FunctorialResolution.EmbeddedResolution
