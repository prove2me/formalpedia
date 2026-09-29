-- Prove2me | solution 1 for GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/692cedf6-a9a8-5962-98cd-43555e9153cc

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow

set_option autoImplicit false

namespace FrobPush

theorem pow_prime_pow_dichotomy {R : Type*} [Monoid R] (p j : ℕ) :
    (∀ x : R, x ^ p ^ 2 = x → x ^ p ^ j = x) ∨ (∀ x : R, x ^ p ^ 2 = x → x ^ p ^ j = x ^ p) := by
  induction j with
  | zero => left; intro x _; simp
  | succ j ih =>
    rcases ih with h | h
    · right; intro x hx; rw [pow_succ, pow_mul, h x hx]
    · left; intro x hx; rw [pow_succ, pow_mul, h x hx, ← pow_mul, ← pow_two, hx]

theorem tameCharacter_pow_sq (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    P.tameCharacter π σ ^ p ^ 2 = P.tameCharacter π σ := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero hp.one_lt))] at hπ
    exact hp0 hπ.symm
  have hsq : p ^ 2 = (p ^ 2 - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)).symm
  unfold ValuationSubring.tameCharacter
  split_ifs with hmem
  · have hx : (⟨σ π / π, hmem⟩ : P) ^ (p ^ 2 - 1) = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, div_pow, ← map_pow, hπ, map_natCast, div_self hp0]
    rw [hsq, pow_succ, ← map_pow, hx, map_one, one_mul]
  · rw [zero_pow (pow_ne_zero 2 hp.ne_zero)]

end FrobPush

open FrobPush in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      GL (Fin 2) (IsLocalRing.ResidueField P))
    (φ : IsLocalRing.ResidueField P →+* IsLocalRing.ResidueField P) (j : ℕ)
    (hφ : ∀ x, φ x = x ^ p ^ j) (kn : ℕ)
    (h : ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ σ).val.mulVec v = P.tameCharacter π σ ^ (kn - 1) • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ σ).val.mulVec v = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v))) :
    ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map φ).mulVec v = P.tameCharacter π σ ^ (kn - 1) • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map φ).mulVec v = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v)) := by
  classical
  obtain ⟨v, hv0, halt⟩ := h
  have hφinj : Function.Injective φ := φ.injective
  refine ⟨φ ∘ v, ?_, ?_⟩
  · intro h0
    apply hv0
    funext i
    apply hφinj
    rw [Pi.zero_apply, map_zero]
    exact congrFun h0 i
  · have key : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ((ρ σ).val.map φ).mulVec (φ ∘ v) = φ ∘ ((ρ σ).val.mulVec v) := by
      intro σ; funext i; exact (RingHom.map_mulVec φ (ρ σ).val v i).symm
    have hsm : ∀ c : IsLocalRing.ResidueField P, φ ∘ (c • v) = φ c • (φ ∘ v) := by
      intro c; funext i; simp [Pi.smul_apply, smul_eq_mul, map_mul]
    have hω : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        P.tameCharacter π σ ^ p ^ 2 = P.tameCharacter π σ := tameCharacter_pow_sq p P π hπ
    rcases pow_prime_pow_dichotomy (R := IsLocalRing.ResidueField P) p j with hj | hj
    · have hφω : ∀ σ, φ (P.tameCharacter π σ) = P.tameCharacter π σ := fun σ => by
        rw [hφ, hj _ (hω σ)]
      rcases halt with hA | hB
      · left
        intro σ hσ
        rw [key, hA σ hσ, hsm, map_pow, hφω]
      · right
        intro σ hσ
        rw [key, hB σ hσ, hsm, map_pow, map_pow, hφω]
    · have hφω : ∀ σ, φ (P.tameCharacter π σ) = P.tameCharacter π σ ^ p := fun σ => by
        rw [hφ, hj _ (hω σ)]
      rcases halt with hA | hB
      · right
        intro σ hσ
        rw [key, hA σ hσ, hsm, map_pow, hφω]
      · left
        intro σ hσ
        rw [key, hB σ hσ, hsm, map_pow, map_pow, hφω, ← pow_mul (P.tameCharacter π σ) p p, ← pow_two p, hω]

end S_GaloisRep_exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow
end P2MW
export P2MW.S_GaloisRep_exists_inertia_eigenvector_tameCharacter_pow_map_of_forall_eq_pow (solution)
