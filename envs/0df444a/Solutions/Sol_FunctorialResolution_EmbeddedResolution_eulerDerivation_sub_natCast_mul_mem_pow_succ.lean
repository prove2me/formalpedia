-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.eulerDerivation_sub_natCast_mul_mem_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:26.991723+00:00
-- url     : https://prove2.me/submissions/c4f670be-0129-479d-a527-3299c0d1eea5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_eulerDerivation_apply_mem_span
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_eulerDerivation_apply_generator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open IsLocalRing
private theorem eulerDerivation_sub_self_mem_sq (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {f : R}
    (hf : f ∈ Ideal.span (Set.range x)) :
    eulerDerivation k x D f - f ∈ Ideal.span (Set.range x) ^ 2 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      rw [eulerDerivation_apply_generator k x D hD j, sub_self]
      exact Submodule.zero_mem _
  | zero =>
      rw [map_zero, sub_zero]
      exact Submodule.zero_mem _
  | add a b _ _ iha ihb =>
      have key : eulerDerivation k x D (a + b) - (a + b)
          = (eulerDerivation k x D a - a) + (eulerDerivation k x D b - b) := by
        rw [map_add]; ring
      rw [key]
      exact Submodule.add_mem _ iha ihb
  | smul c a ha iha =>
      have key : eulerDerivation k x D (c • a) - c • a
          = c * (eulerDerivation k x D a - a) + a * eulerDerivation k x D c := by
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
      rw [key]
      refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ iha) ?_
      have h2 := Ideal.mul_mem_mul ha (eulerDerivation_apply_mem_span k x D c)
      rwa [← pow_two] at h2
private theorem forall_eulerDerivation_sub_natCast_mul_mem (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (r : ℕ) :
    ∀ f : R, f ∈ Ideal.span (Set.range x) ^ r →
      eulerDerivation k x D f - (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  induction r with
  | zero =>
      intro f _
      have h := eulerDerivation_apply_mem_span k x D f
      simpa using h
  | succ r ih =>
      intro f hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        have hEb := eulerDerivation_sub_self_mem_sq k x D hD hb
        have hEa := ih a ha
        have h1 : a * (eulerDerivation k x D b - b) ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          have h := Ideal.mul_mem_mul ha hEb
          rwa [← pow_add] at h
        have h2 : (eulerDerivation k x D a - (r : R) * a) * b
            ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          have hb1 : b ∈ Ideal.span (Set.range x) ^ 1 := by rwa [pow_one]
          have h := Ideal.mul_mem_mul hEa hb1
          have e : r + 1 + 1 = r + 2 := by omega
          rw [← pow_add, e] at h
          exact h
        have key : eulerDerivation k x D (a * b) - ((r + 1 : ℕ) : R) * (a * b)
            = a * (eulerDerivation k x D b - b) + (eulerDerivation k x D a - (r : R) * a) * b := by
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
          push_cast
          ring
        have hres : eulerDerivation k x D (a * b) - ((r + 1 : ℕ) : R) * (a * b)
            ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          rw [key]
          exact Submodule.add_mem _ h1 h2
        exact hres
      · intro y z hy hz
        have key : eulerDerivation k x D (y + z) - ((r + 1 : ℕ) : R) * (y + z)
            = (eulerDerivation k x D y - ((r + 1 : ℕ) : R) * y)
              + (eulerDerivation k x D z - ((r + 1 : ℕ) : R) * z) := by
          rw [map_add]; ring
        have hres : eulerDerivation k x D (y + z) - ((r + 1 : ℕ) : R) * (y + z)
            ∈ Ideal.span (Set.range x) ^ (r + 1 + 1) := by
          rw [key]
          exact Submodule.add_mem _ hy hz
        exact hres
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (r : ℕ) {f : R}
    (hf : f ∈ Ideal.span (Set.range x) ^ r) :
    eulerDerivation k x D f - (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) :=
  forall_eulerDerivation_sub_natCast_mul_mem k x D hD r f hf
end FunctorialResolution.EmbeddedResolution
