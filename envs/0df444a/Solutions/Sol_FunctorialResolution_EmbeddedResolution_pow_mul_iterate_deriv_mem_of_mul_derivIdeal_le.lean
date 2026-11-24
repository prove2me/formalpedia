-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:12.43888+00:00
-- url     : https://prove2.me/submissions/fd522a35-b04a-4161-b02c-6f576cceb3ef

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeriesRingHom_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply


section
namespace FunctorialResolution.EmbeddedResolution
section
variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
private theorem exists_mul_deriv_pow_eq_pow_mul {k : Type*} [CommRing k] {S : Type*}
    [CommRing S] [Algebra k S] (Δ : Derivation k S S) (b : S) (n : ℕ) :
    ∃ c : S, b * Δ (b ^ n) = b ^ n * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + Δ b, ?_⟩
      have hbp : b ^ (m + 1) = b * b ^ m := by ring
      have hl : Δ (b * b ^ m) = b * Δ (b ^ m) + b ^ m * Δ b := by
        simp
      rw [hbp, hl]
      linear_combination b * hc
end
section
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
end
section
open IsLocalRing
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (M J : Ideal S) (Δ : Derivation k S S) (b : S)
    (hMJ : M * derivIdeal k J ≤ J) (hb : b ∈ M) :
    ∀ (j : ℕ) (g : S), g ∈ J → b ^ j * (⇑Δ)^[j] g ∈ J := by
  intro j
  induction j with
  | zero =>
      intro g hg
      simpa using hg
  | succ j ih =>
      intro g hg
      have hIH : b ^ j * (⇑Δ)^[j] g ∈ J := ih g hg
      have hkey : b * Δ (b ^ j * (⇑Δ)^[j] g) ∈ J :=
        hMJ (Ideal.mul_mem_mul hb (derivation_apply_mem_derivIdeal k J Δ hIH))
      obtain ⟨c, hc⟩ := exists_mul_deriv_pow_eq_pow_mul Δ b j
      have hleib : Δ (b ^ j * (⇑Δ)^[j] g)
          = b ^ j * Δ ((⇑Δ)^[j] g) + (⇑Δ)^[j] g * Δ (b ^ j) := by
        simp
      have hiter : (⇑Δ)^[j + 1] g = Δ ((⇑Δ)^[j] g) := Function.iterate_succ_apply' (⇑Δ) j g
      have hEq : b ^ (j + 1) * (⇑Δ)^[j + 1] g
          = b * Δ (b ^ j * (⇑Δ)^[j] g) - c * (b ^ j * (⇑Δ)^[j] g) := by
        rw [hiter, hleib]
        linear_combination (-((⇑Δ)^[j] g)) * hc
      rw [hEq]
      exact Submodule.sub_mem J hkey (Ideal.mul_mem_left J c hIH)
end FunctorialResolution.EmbeddedResolution
