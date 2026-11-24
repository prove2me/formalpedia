-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeries_sub_mem_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:59.305579+00:00
-- url     : https://prove2.me/submissions/41a926aa-1dd6-4eea-8b54-f3067938936f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.TaylorExpansion
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
namespace FunctorialResolution.EmbeddedResolution.TaylorExpansion
theorem _root_.solution (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 1 ≤ N) (f : R) :
    truncatedSeries σ D β N f - σ f ∈ Ideal.span ({β} : Set S) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hN).symm⟩
  have key : truncatedSeries σ D β (M + 1) f - σ f =
      ∑ j ∈ Finset.range M,
        algebraMap ℚ S (((j + 1).factorial : ℚ)⁻¹) * σ ((⇑D)^[j + 1] f) * β ^ (j + 1) := by
    rw [truncatedSeries_apply, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Ideal.mem_span_singleton]
  exact dvd_mul_of_dvd_right (dvd_pow_self β j.succ_ne_zero) _
end FunctorialResolution.EmbeddedResolution.TaylorExpansion
