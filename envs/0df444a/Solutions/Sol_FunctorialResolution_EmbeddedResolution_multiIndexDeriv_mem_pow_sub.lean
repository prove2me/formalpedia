-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.multiIndexDeriv_mem_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:59.614792+00:00
-- url     : https://prove2.me/submissions/c5797fc8-e86e-45a8-af8b-3680f70adaf3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
section
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
private theorem mul_pow_sub_one_le (J : Ideal R) (n : ℕ) :
    J * J ^ (n - 1) ≤ J ^ n := by
  cases n with
  | zero =>
      show J * J ^ 0 ≤ J ^ 0
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
  | succ m =>
      show J * J ^ m ≤ J ^ (m + 1)
      exact le_of_eq (by rw [mul_comm, ← pow_succ])
private theorem derivation_mem_pow_sub_one (J : Ideal R) (D : Derivation k R R) :
    ∀ (n : ℕ) (f : R), f ∈ J ^ n → D f ∈ J ^ (n - 1) := by
  intro n
  induction n with
  | zero =>
      intro f _
      show D f ∈ J ^ 0
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ m ih =>
      intro f hf
      rw [pow_succ] at hf
      show D f ∈ J ^ m
      refine Submodule.mul_induction_on (C := fun x => D x ∈ J ^ m) hf ?_ ?_
      · intro a ha b hb
        have hDa : D a ∈ J ^ (m - 1) := ih a ha
        have hL : D (a * b) = a * D b + b * D a := by
          rw [D.leibniz, smul_eq_mul, smul_eq_mul]
        show D (a * b) ∈ J ^ m
        rw [hL]
        refine Submodule.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
        exact mul_pow_sub_one_le J m (Ideal.mul_mem_mul hb hDa)
      · intro x y hx hy
        show D (x + y) ∈ J ^ m
        rw [map_add]
        exact Submodule.add_mem _ hx hy
private theorem iterate_derivation_mem_pow_sub (J : Ideal R) (D : Derivation k R R) :
    ∀ (m n : ℕ) (f : R), f ∈ J ^ n → (⇑D)^[m] f ∈ J ^ (n - m) := by
  intro m
  induction m with
  | zero =>
      intro n f hf
      rw [Function.iterate_zero_apply, Nat.sub_zero]
      exact hf
  | succ m ih =>
      intro n f hf
      rw [Function.iterate_succ_apply]
      have h1 : D f ∈ J ^ (n - 1) := derivation_mem_pow_sub_one J D n f hf
      have h2 := ih (n - 1) (D f) h1
      have h3 : n - 1 - m = n - (m + 1) := by omega
      rw [h3] at h2
      exact h2
private theorem foldr_iterate_mem_pow_sub (J : Ideal R) :
    ∀ (h : ℕ) (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (n : ℕ) (f : R), f ∈ J ^ n →
      Fin.foldr h (fun i y => (⇑(D i))^[α i] y) f ∈ J ^ (n - ∑ i, α i) := by
  intro h
  induction h with
  | zero =>
      intro D α n f hf
      have hz : ∑ i : Fin 0, α i = 0 := by simp
      rw [Fin.foldr_zero, hz, Nat.sub_zero]
      exact hf
  | succ h ih =>
      intro D α n f hf
      have hinner : Fin.foldr h (fun i y => (⇑(D i.succ))^[α i.succ] y) f
          ∈ J ^ (n - ∑ i : Fin h, α i.succ) :=
        ih (fun i => D i.succ) (fun i => α i.succ) n f hf
      have h2 := iterate_derivation_mem_pow_sub J (D 0) (α 0)
        (n - ∑ i : Fin h, α i.succ) _ hinner
      have hs0 : ∑ i, α i = α 0 + ∑ i : Fin h, α i.succ := Fin.sum_univ_succ α
      have hs : n - ∑ i, α i = n - (∑ i : Fin h, α i.succ) - α 0 := by
        rw [hs0]; omega
      rw [Fin.foldr_succ, hs]
      exact h2
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {h : ℕ} (D : Fin h → Derivation k R R) (J : Ideal R) (n : ℕ)
    {f : R} (hf : f ∈ J ^ n) (α : Fin h → ℕ) :
    multiIndexDeriv D α f ∈ J ^ (n - ∑ i, α i) := by
  exact foldr_iterate_mem_pow_sub J h D α n f hf
end FunctorialResolution.EmbeddedResolution
