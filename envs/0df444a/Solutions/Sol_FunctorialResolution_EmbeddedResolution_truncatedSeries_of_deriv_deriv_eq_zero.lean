-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.truncatedSeries_of_deriv_deriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:51.427652+00:00
-- url     : https://prove2.me/submissions/c38fe6d6-ae6e-4bdb-bf11-15d1bfe2c59d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeriesRingHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply



set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 2 ≤ N) (f : R) (hf : D (D f) = 0) :
    TaylorExpansion.truncatedSeries σ D β N f = σ f + σ (D f) * β := by
  have h2 : (⇑D)^[2] f = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
    simp [hf]
  have hvan : ∀ j : ℕ, 2 ≤ j → (⇑D)^[j] f = 0 := by
    intro j hj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm, Function.iterate_add_apply, h2]
    exact Function.iterate_fixed (by simp) m
  have hsub : Finset.range 2 ⊆ Finset.range N := fun j hj =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hN)
  have hsum : ∑ j ∈ Finset.range 2,
        algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j
      = ∑ j ∈ Finset.range N,
        algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j := by
    refine Finset.sum_subset hsub ?_
    intro j _ hj
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · exact absurd (Finset.mem_range.mpr h) hj
      · exact h
    rw [hvan j hj2]
    simp
  rw [TaylorExpansion.truncatedSeries_apply, ← hsum]
  simp [Finset.sum_range_succ]
end FunctorialResolution.EmbeddedResolution
