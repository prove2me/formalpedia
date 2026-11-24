-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:48.230209+00:00
-- url     : https://prove2.me/submissions/67d82612-5cf6-42f7-aa65-afaa743f02d5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
private theorem derivation_apply_mem_pow_of_mem_pow_succ {k : Type*} [CommRing k] {S : Type*}
    [CommRing S] [Algebra k S] (J : Ideal S) (D : Derivation k S S) :
    ∀ n : ℕ, ∀ x ∈ J ^ (n + 1), D x ∈ J ^ n := by
  intro n
  induction n with
  | zero =>
      intro x _
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        simp only [Derivation.leibniz, smul_eq_mul]
        refine Submodule.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
        have hb' : D a * b ∈ J ^ n * J := Ideal.mul_mem_mul (ih a ha) hb
        rw [← pow_succ] at hb'
        rw [mul_comm b (D a)]
        exact hb'
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
private theorem pow_succ_le_pow {S : Type*} [CommRing S] (J : Ideal S) (m : ℕ) :
    J ^ (m + 1) ≤ J ^ m := by
  rw [pow_succ]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right s _ hr
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) (n : ℕ) : derivIdeal k (J ^ n) ≤ J ^ (n - 1) := by
  obtain _ | m := n
  · have h : (J ^ (0 - 1 : ℕ) : Ideal S) = ⊤ := by simp
    exact le_top.trans h.ge
  · have key : derivIdeal k (J ^ (m + 1)) ≤ J ^ m := by
      rw [derivIdeal_le_iff]
      exact ⟨pow_succ_le_pow J m,
        fun D x hx => derivation_apply_mem_pow_of_mem_pow_succ J D m x hx⟩
    exact key
end FunctorialResolution.EmbeddedResolution
