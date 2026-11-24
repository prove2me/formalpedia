-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivation_apply_mem_derivIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:43.39685+00:00
-- url     : https://prove2.me/submissions/eed908d6-a84d-4366-a0b6-626c856748a1

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
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] (J : Ideal S) (D : Derivation k S S) {x : S} (hx : x ∈ J) :
    D x ∈ derivIdeal k J := by
  rw [derivIdeal_eq_sup_span]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨D, x, hx, rfl⟩)
end FunctorialResolution.EmbeddedResolution
