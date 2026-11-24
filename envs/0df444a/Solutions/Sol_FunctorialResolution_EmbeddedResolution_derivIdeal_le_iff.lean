-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:43.756417+00:00
-- url     : https://prove2.me/submissions/7e364cd9-b904-414b-b4ee-4becf9142470

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
private theorem derivIdeal_eq_sup_span (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) :
    derivIdeal k J = J ⊔ Ideal.span {x : S | ∃ D : Derivation k S S, ∃ y ∈ J, D y = x} := rfl
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J K : Ideal S) :
    derivIdeal k J ≤ K ↔ J ≤ K ∧ ∀ D : Derivation k S S, ∀ x ∈ J, D x ∈ K := by
  rw [derivIdeal_eq_sup_span, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun D x hx => h2 ⟨D, x, hx, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro x ⟨D, y, hy, rfl⟩
    exact h2 D y hy
end FunctorialResolution.EmbeddedResolution
