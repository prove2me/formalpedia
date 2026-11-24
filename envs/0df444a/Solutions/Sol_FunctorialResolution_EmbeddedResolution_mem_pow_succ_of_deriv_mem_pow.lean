-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_pow_succ_of_deriv_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:14.709085+00:00
-- url     : https://prove2.me/submissions/30fad9a4-3086-4680-9d56-742a5fbdf1e3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_eulerDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_eulerDerivation_sub_natCast_mul_mem_pow_succ

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
theorem _root_.solution (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
    {f : R} (hf : f ∈ Ideal.span (Set.range x) ^ r)
    (hdf : ∀ i, D i f ∈ Ideal.span (Set.range x) ^ r) :
    f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  have hgen : ∀ i, x i * D i f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    intro i
    have hx1 : x i ∈ Ideal.span (Set.range x) ^ 1 := by
      rw [pow_one]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h := Ideal.mul_mem_mul hx1 (hdf i)
    rw [← pow_add, Nat.add_comm 1 r] at h
    exact h
  have h1 : eulerDerivation k x D f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    rw [eulerDerivation_apply]
    exact Ideal.sum_mem _ fun i _ => hgen i
  have h2 := eulerDerivation_sub_natCast_mul_mem_pow_succ k x D hD r hf
  have h3 : (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    have h := Submodule.sub_mem _ h1 h2
    simpa using h
  obtain ⟨u, hu⟩ := hr
  have key : (↑u⁻¹ : R) * ((r : R) * f) = f := by
    rw [← hu, ← mul_assoc, u.inv_mul, one_mul]
  rw [← key]
  exact Ideal.mul_mem_left _ _ h3
end FunctorialResolution.EmbeddedResolution
