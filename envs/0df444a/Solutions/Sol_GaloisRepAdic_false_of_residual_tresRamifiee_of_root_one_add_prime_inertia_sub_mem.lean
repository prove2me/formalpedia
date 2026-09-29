-- Prove2me | solution 1 for GaloisRepAdic.false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d5d5da70-3c4f-5dc9-9458-9436f56f72ff

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem

set_option autoImplicit false

namespace GaloisRepAdic
p2m_export "GaloisRepAdic" "residual ρ V"
namespace K5SAux
p2m_open "GaloisRepAdic"

open scoped TensorProduct

theorem norm_natCast_prime (p : ℕ) [Fact p.Prime] : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_one_add_prime (p : ℕ) [Fact p.Prime] : ‖(1 + p : PadicAlgCl p)‖ = 1 := by
  have hp : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hne : ‖(1 : PadicAlgCl p)‖ ≠ ‖(p : PadicAlgCl p)‖ := by
    rw [norm_one, norm_natCast_prime]
    exact hp.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, norm_natCast_prime,
    max_eq_left hp.le]

theorem one_add_prime_ne_zero (p : ℕ) [Fact p.Prime] : (1 + p : PadicAlgCl p) ≠ 0 :=
  fun h => by simpa [h] using norm_one_add_prime p

theorem valuation_one_add_prime (p : ℕ) [Fact p.Prime] :
    (padicPlace p).valuation (1 + p : AlgebraicClosure ℚ) = 1 := by
  have hι : padicEmbedding p (1 + p : AlgebraicClosure ℚ) = 1 + p := by
    rw [map_add, map_one, map_natCast]
  have h0 : (1 + p : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    apply one_add_prime_ne_zero p
    rw [← hι, h, map_zero]
  apply le_antisymm
  · rw [ValuationSubring.valuation_le_one_iff, mem_padicPlace_iff, hι, ← NNReal.coe_le_coe,
      coe_nnnorm, norm_one_add_prime, NNReal.coe_one]
  · rw [Valuation.one_le_val_iff _ h0, ValuationSubring.valuation_le_one_iff, mem_padicPlace_iff,
      map_inv₀, hι, nnnorm_inv, ← NNReal.coe_le_coe, NNReal.coe_inv, coe_nnnorm,
      norm_one_add_prime, inv_one, NNReal.coe_one]

theorem exists_pow_eq_one_padicEmbedding_eq (p : ℕ) [Fact p.Prime] (ξ : PadicAlgCl p)
    (hξ : ξ ^ p = 1) :
    ∃ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 ∧ padicEmbedding p ζ = ξ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure ℚ) (n := p)
  have hζ' : IsPrimitiveRoot (padicEmbedding p ζ) p :=
    hζ.map_of_injective (padicEmbedding p).toRingHom.injective
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hξ
  refine ⟨ζ ^ i, ?_, by rw [map_pow, hi]⟩
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem tmul_residueField_eq_zero_of_mem_maximalIdeal_smul {B : Type} [CommRing B]
    [IsLocalRing B] {V : Type} [AddCommGroup V] [Module B V] {x : V}
    (hx : x ∈ (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B V))
    (c : IsLocalRing.ResidueField B) :
    c ⊗ₜ[B] x = (0 : IsLocalRing.ResidueField B ⊗[B] V) := by
  refine Submodule.smul_induction_on
    (p := fun x => c ⊗ₜ[B] x = (0 : IsLocalRing.ResidueField B ⊗[B] V)) hx ?_ ?_
  · intro a ha w _
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).mpr ha,
      zero_mul, TensorProduct.zero_tmul]
  · intro x y hx hy
    rw [TensorProduct.tmul_add, hx, hy, add_zero]

end GaloisRepAdic.K5SAux

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] (p : ℕ) [Fact p.Prime] (ρ : GaloisRepAdic B)
    (β : PadicAlgCl p) (hβ : β ^ p = 1 + (p : PadicAlgCl p))
    (hsplit : ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ξ : PadicAlgCl p, ξ ^ p = 1 → τ ξ = ξ) → τ β = β →
          ∀ v : ρ.V, ρ.ρ (localGaloisToGlobal p τ) v - v ∈
            (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B ρ.V))
    (htres : ∀ (n : ℕ) (u β : Fin n → AlgebraicClosure ℚ),
        (∀ i, (padicPlace p).valuation (u i) = 1) →
        (∀ i, ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, σ (u i) = u i) →
        (∀ i, β i ^ p = u i) →
        ∃ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ) ∧ (∀ i, σ (β i) = β i) ∧
            ρ.residual.ρ σ ≠ 1) :
    False := by

  obtain ⟨β₀, hβ₀⟩ :=
    IsAlgClosed.exists_pow_nat_eq (1 + p : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos

  obtain ⟨σ, hσI, hσζ, hσβ, hσρ⟩ := htres 1 (fun _ => 1 + p) (fun _ => β₀)
    (fun _ => GaloisRepAdic.K5SAux.valuation_one_add_prime p)
    (fun _ σ _ => by simp only [map_add, map_one, map_natCast])
    (fun _ => hβ₀)
  have hσβ₀ : σ β₀ = β₀ := hσβ 0

  obtain ⟨τ, hτI, hτσ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq p σ hσI
  subst hτσ

  have hτξ : ∀ ξ : PadicAlgCl p, ξ ^ p = 1 → τ ξ = ξ := by
    intro ξ hξ
    obtain ⟨ζ, hζ, rfl⟩ := GaloisRepAdic.K5SAux.exists_pow_eq_one_padicEmbedding_eq p ξ hξ
    rw [← padicEmbedding_localGaloisToGlobal, hσζ ζ hζ]

  have hιβ₀ : padicEmbedding p β₀ ^ p = 1 + p := by
    rw [← map_pow, hβ₀, map_add, map_one, map_natCast]
  have hιβ₀0 : padicEmbedding p β₀ ≠ 0 := by
    intro h0
    apply GaloisRepAdic.K5SAux.one_add_prime_ne_zero p
    rw [← hιβ₀, h0, zero_pow (Fact.out : p.Prime).ne_zero]
  have hξ : (β * (padicEmbedding p β₀)⁻¹) ^ p = 1 := by
    rw [mul_pow, inv_pow, hβ, hιβ₀, mul_inv_cancel₀ (GaloisRepAdic.K5SAux.one_add_prime_ne_zero p)]
  have hτβ : τ β = β := by
    have key : τ (β * (padicEmbedding p β₀)⁻¹ * padicEmbedding p β₀) =
        β * (padicEmbedding p β₀)⁻¹ * padicEmbedding p β₀ := by
      rw [map_mul, hτξ _ hξ, ← padicEmbedding_localGaloisToGlobal, hσβ₀]
    rwa [mul_assoc, inv_mul_cancel₀ hιβ₀0, mul_one] at key

  have hmod := hsplit τ hτI hτξ hτβ

  apply hσρ
  change (ρ.ρ (localGaloisToGlobal p τ)).baseChange (IsLocalRing.ResidueField B) = 1
  refine LinearMap.ext fun w => ?_
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c v =>
    rw [LinearMap.baseChange_tmul, Module.End.one_apply, ← sub_eq_zero, ← TensorProduct.tmul_sub]
    exact GaloisRepAdic.K5SAux.tmul_residueField_eq_zero_of_mem_maximalIdeal_smul (hmod v) c
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end S_GaloisRepAdic_false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem
end P2MW
export P2MW.S_GaloisRepAdic_false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem (solution)
