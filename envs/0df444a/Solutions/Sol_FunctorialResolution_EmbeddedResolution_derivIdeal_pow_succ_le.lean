-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_pow_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:12.686108+00:00
-- url     : https://prove2.me/submissions/237d2b45-e46b-4b56-abe3-c806381edd1b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
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
private theorem derivation_apply_mem_pow_mul_derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] (J : Ideal S) (D : Derivation k S S) :
    ∀ n : ℕ, ∀ x ∈ J ^ (n + 1), D x ∈ J ^ n * derivIdeal k J := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx' : x ∈ J := by simpa using hx
      have h := derivation_apply_mem_derivIdeal k J D hx'
      simpa using h
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        have hL : D (a * b) = a * D b + b * D a := by
          rw [D.leibniz, smul_eq_mul, smul_eq_mul]
        rw [hL]
        refine Submodule.add_mem _ ?_ ?_
        · exact Ideal.mul_mem_mul ha (derivation_apply_mem_derivIdeal k J D hb)
        · have h2 : b * D a ∈ J * (J ^ n * derivIdeal k J) :=
            Ideal.mul_mem_mul hb (ih a ha)
          have h3 : J * (J ^ n * derivIdeal k J) = J ^ (n + 1) * derivIdeal k J := by
            rw [← mul_assoc, pow_succ, mul_comm J (J ^ n)]
          rwa [h3] at h2
      · intro y z hy hz
        simpa using Submodule.add_mem _ hy hz
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) (n : ℕ) : derivIdeal k (J ^ (n + 1)) ≤ J ^ n * derivIdeal k J := by
  rw [derivIdeal_le_iff]
  refine ⟨?_, ?_⟩
  · rw [pow_succ]
    exact Ideal.mul_le.mpr fun a ha b hb => Ideal.mul_mem_mul ha (le_derivIdeal k J hb)
  · intro D x hx
    exact derivation_apply_mem_pow_mul_derivIdeal k J D n x hx
end FunctorialResolution.EmbeddedResolution
