-- Prove2me | solution 1 for FrobeniusDensity.exists_frobenius_conj_of_mul_self_eq_one_of_statement
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7db11e33-485a-526c-864a-4e306e1a6c1c

import Theorems.Thm_NumberField_exists_isFrobenius_lift_arithFrobAt
import Theorems.Thm_NumberField_exists_valuationSubring_eq_localization
import Theorems.Thm_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement

open scoped NumberField Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

noncomputable section

namespace P2mWs11A1

section S0
variable (L : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ L]

noncomputable abbrev galoisLevel : IntermediateField ℚ ℚ̄ := IntermediateField.normalClosure ℚ L ℚ̄

scoped instance : FiniteDimensional ℚ (galoisLevel L) := normalClosure.is_finiteDimensional ℚ L ℚ̄
scoped instance : IsGalois ℚ (galoisLevel L) := IsGalois.normalClosure ℚ L ℚ̄
scoped instance : NumberField (galoisLevel L) := NumberField.mk

omit [FiniteDimensional ℚ L] in
theorem le_galoisLevel : L ≤ galoisLevel L := IntermediateField.le_normalClosure L

end S0

theorem exists_pow_pow_eq {G : Type*} [Group G] [Finite G] (g : G) {k : ℕ} (hk : k.Coprime (orderOf g)) :
    ∃ j : ℕ, (g ^ k) ^ j = g := by
  rcases Nat.lt_or_ge 1 (orderOf g) with h1 | h1
  · obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk h1
    refine ⟨j, ?_⟩
    rw [← pow_mul, ← pow_mod_orderOf, hj, pow_one]
  · refine ⟨0, ?_⟩
    have : orderOf g = 1 := le_antisymm h1 (orderOf_pos g)
    rw [pow_zero, eq_comm, ← orderOf_eq_one_iff, this]

theorem pow_eq_self_of_mul_self_eq_one {G : Type*} [Group G] (g : G) (hg : g * g = 1) {k : ℕ}
    (hk : k.Coprime (orderOf g)) : g ^ k = g := by
  have h2 : g ^ 2 = 1 := by rw [sq]; exact hg
  have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h2'
  · rw [orderOf_eq_one_iff.mp h1, one_pow]
  · rw [h2'] at hk
    have hodd : k % 2 = 1 := Nat.odd_iff.mp (Nat.Coprime.odd_of_right hk)
    rw [← pow_mod_orderOf, h2', hodd, pow_one]

end P2mWs11A1
p2m_reactivate "P2MW.S_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement.P2mWs11A1"

end
p2m_reactivate "P2MW.S_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement.P2mWs11A1"

open P2mWs11A1 in
theorem solution
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ * σ = 1) (S : Finset ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
      ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ ∀ x ∈ L, σ x = (γ * τ * γ⁻¹) x := by

  obtain ⟨ℓ, hℓS, hℓ, hreal⟩ := hFD (galoisLevel L) (σ.restrictNormal (galoisLevel L)) S

  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 (galoisLevel L)) (FrobeniusDensity.ratPrimeIdeal ℓ)
  haveI := hQmax; haveI := hQover
  haveI : Finite (𝓞 (galoisLevel L) ⧸ Q) :=
    FrobeniusDensity.finite_quotient_of_ne_bot (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  obtain ⟨k, hk, hconj⟩ := hreal Q inferInstance inferInstance inferInstance

  obtain ⟨Qt, hQt, τ, hQtQ, hres, hstab, hfrob⟩ := NumberField.exists_isFrobenius_lift_arithFrobAt (galoisLevel L) ℓ hℓ Q
  obtain ⟨A, hA⟩ := NumberField.exists_valuationSubring_eq_localization Qt
  have hℓQt : ((ℓ : ℕ) : 𝓞 ℚ̄) ∈ Qt := by
    have h1 : ((ℓ : ℤ) : 𝓞 (galoisLevel L)) ∈ Q := by
      have := (Ideal.mem_of_liesOver Q (FrobeniusDensity.ratPrimeIdeal ℓ) (ℓ : ℤ)).mp
        (Ideal.mem_span_singleton_self _)
      simpa using this
    have h2 := (Ideal.mem_of_liesOver Qt Q ((ℓ : ℤ) : 𝓞 (galoisLevel L))).mp h1
    simpa using h2
  obtain ⟨hAℓ, hAτ⟩ := ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem Qt ℓ hℓ hℓQt τ hstab hfrob A hA

  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hσ' : σ.restrictNormal (galoisLevel L) * σ.restrictNormal (galoisLevel L) = 1 := by
    change AlgEquiv.restrictNormalHom (galoisLevel L) σ * AlgEquiv.restrictNormalHom (galoisLevel L) σ = 1
    rw [← map_mul, hσ, map_one]
  have hj : σ.restrictNormal (galoisLevel L) ^ k = σ.restrictNormal (galoisLevel L) :=
    pow_eq_self_of_mul_self_eq_one _ hσ' hk
  obtain ⟨γ, hγ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := galoisLevel L) (E := AlgebraicClosure ℚ) c⁻¹
  refine ⟨ℓ, hℓ, hℓS, A, τ, γ, hAℓ, hAτ, fun x hx => ?_⟩
  have key : (γ * τ * γ⁻¹).restrictNormal (galoisLevel L) = σ.restrictNormal (galoisLevel L) := by
    have hγ' : γ.restrictNormal (galoisLevel L) = c⁻¹ := hγ
    have e1 : (γ * τ * γ⁻¹).restrictNormal (galoisLevel L)
        = γ.restrictNormal (galoisLevel L) * τ.restrictNormal (galoisLevel L) * (γ.restrictNormal (galoisLevel L))⁻¹ := by
      change AlgEquiv.restrictNormalHom (galoisLevel L) (γ * τ * γ⁻¹) = AlgEquiv.restrictNormalHom (galoisLevel L) γ
        * AlgEquiv.restrictNormalHom (galoisLevel L) τ * (AlgEquiv.restrictNormalHom (galoisLevel L) γ)⁻¹
      rw [map_mul, map_mul, map_inv]
    have hsk : σ.restrictNormal (galoisLevel L) ^ k = c⁻¹ * τ.restrictNormal (galoisLevel L) * c⁻¹⁻¹ := by
      rw [inv_inv, hres, ← hc]; simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [e1, hγ', ← hj, hsk]
  have hxE : x ∈ (galoisLevel L) := le_galoisLevel L hx
  have e2 := AlgEquiv.restrictNormal_commutes (γ * τ * γ⁻¹) (galoisLevel L) ⟨x, hxE⟩
  have e3 := AlgEquiv.restrictNormal_commutes σ (galoisLevel L) ⟨x, hxE⟩
  rw [key] at e2

  change (algebraMap (galoisLevel L) ℚ̄) ((σ.restrictNormal (galoisLevel L)) ⟨x, hxE⟩) = (γ * τ * γ⁻¹) x at e2
  change (algebraMap (galoisLevel L) ℚ̄) ((σ.restrictNormal (galoisLevel L)) ⟨x, hxE⟩) = σ x at e3
  rw [← e2, ← e3]

end S_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement
end P2MW
export P2MW.S_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement (solution)
