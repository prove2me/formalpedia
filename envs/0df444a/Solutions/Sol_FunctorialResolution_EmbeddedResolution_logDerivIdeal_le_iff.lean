-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdeal_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:25.55971+00:00
-- url     : https://prove2.me/submissions/e022456b-c0ef-4bb1-a1eb-72750beb9350

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
private theorem logDerivIdeal_eq_sup_span (P J : Ideal S) :
    logDerivIdeal k P J =
      J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x} := rfl
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (P J K : Ideal S) :
    logDerivIdeal k P J ≤ K ↔
      J ≤ K ∧ ∀ D ∈ tangentDerivations k P, ∀ x ∈ J, D x ∈ K := by
  rw [logDerivIdeal_eq_sup_span, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun D hD x hx => h2 ⟨D, hD, x, hx, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro x ⟨D, hD, y, hy, rfl⟩
    exact h2 D hD y hy
end FunctorialResolution.EmbeddedResolution
