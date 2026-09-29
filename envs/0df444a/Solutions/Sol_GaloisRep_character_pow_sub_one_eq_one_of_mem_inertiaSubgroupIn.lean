-- Prove2me | solution 1 for GaloisRep.character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ed394b32-a053-5c17-9ad1-c16e5da2c5ac

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn

set_option autoImplicit false

namespace GaloisRep
namespace CharacterInertiaAux

theorem normal_rat_algebraicClosure : Normal ℚ (AlgebraicClosure ℚ) := by
  have h1 : (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ)) = AlgebraicClosure.instAlgebra ℚ :=
    Subsingleton.elim _ _
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by rw [h1]; infer_instance
  exact ⟨fun x => IsAlgClosed.splits _⟩

theorem exists_normal_level (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] :
    ∃ L' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L' ∧ Normal ℚ L' ∧ L ≤ L' := by
  haveI := normal_rat_algebraicClosure
  exact ⟨IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ), normalClosure.is_finiteDimensional ℚ L _,
    normalClosure.normal ℚ L _, IntermediateField.le_normalClosure L⟩

end GaloisRep.CharacterInertiaAux

open GaloisRep.CharacterInertiaAux in

theorem solution
    {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Kˣ)
    (hχ : GaloisFactorsThroughFiniteLevel χ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    χ τ ^ (p - 1) = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨L, hLfd, hL⟩ := hχ
  haveI := hLfd
  obtain ⟨L', hL'fd, hL'n, hLL'⟩ := exists_normal_level L
  haveI := hL'fd
  haveI := hL'n
  have hL' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L', σ x = x) → χ σ = 1 :=
    fun σ h => hL σ (fun x hx => h x (hLL' hx))
  obtain ⟨φ, hφ⟩ := ValuationSubring.exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime hp P hP
  obtain ⟨-, hwild⟩ := hφ τ hτ
  obtain ⟨a, ha⟩ :=
    ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild hp P hP hwild L'
  set w := φ * τ * φ⁻¹ * (τ ^ p)⁻¹ with hw
  have h1 : χ w ^ p ^ a = 1 := by
    rw [← map_pow]
    exact hL' _ ha

  have h2 : χ w = 1 := by
    have hx : ((χ w : K) - 1) ^ p ^ a = 0 := by
      rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, sub_self]
    have hx' : (χ w : K) = 1 := sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero a hp.ne_zero) |>.mp hx)
    exact Units.val_eq_one.mp hx'

  have h3 : χ w = χ τ * (χ τ ^ p)⁻¹ := by
    rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, mul_right_comm (χ φ) (χ τ) (χ φ)⁻¹,
      mul_inv_cancel, one_mul]
  rw [h3, mul_inv_eq_one] at h2

  have h4 : χ τ ^ (p - 1) * χ τ = 1 * χ τ := by
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le, one_mul]
    exact h2.symm
  exact mul_right_cancel h4

end S_GaloisRep_character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_GaloisRep_character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn (solution)
