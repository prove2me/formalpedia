-- Prove2me | solution 1 for GaloisRep.det_eq_cycloChar_pow_of_det_frobenius_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7bb37c37-a329-5b65-8fee-597eac171574

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_MonoidHom_isOpen_ker_of_cycloCharSpec
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_det_eq_cycloChar_pow_of_det_frobenius_eq_pow
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

namespace GaloisRep
namespace DetFrobAux

theorem isOpen_ker_of_galoisFactorsThroughFiniteLevel {M : Type} [Group M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M) (hfin : GaloisFactorsThroughFiniteLevel ρ) :
    IsOpen ((ρ.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
  obtain ⟨L, hL, hker⟩ := hfin
  haveI := hL
  refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen L)
  intro σ hσ
  rw [MonoidHom.mem_ker]
  exact hker σ ((IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ)

end GaloisRep.DetFrobAux

open GaloisRep.DetFrobAux in
theorem solution
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod p)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ p = 1 → σ μ = μ ^ ((cyc σ : ZMod p)).val)
    (N : ℕ) [NeZero N] (S : Set ℕ) (hSfin : S.Finite) (m : ℕ)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          Matrix.det (ρ σ).val = (ℓ : F) ^ m)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Matrix.det (ρ σ).val = ((ZMod.castHom (dvd_refl p) F) (cyc σ : ZMod p)) ^ m := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set cast : ZMod p →+* F := ZMod.castHom (dvd_refl p) F with hcast_def

  set ψ₁ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Fˣ :=
    Matrix.GeneralLinearGroup.det.comp ρ with hψ₁
  set ψ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Fˣ :=
    (Units.map (cast : ZMod p →* F)).comp cyc with hψ₂
  set Φ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Fˣ := ψ₁ * (ψ₂ ^ m)⁻¹ with hΦ
  have hΦ_apply : ∀ τ, Φ τ = ψ₁ τ * ((ψ₂ τ) ^ m)⁻¹ := fun τ => rfl
  have hψ₁_val : ∀ τ, ((ψ₁ τ : Fˣ) : F) = Matrix.det (ρ τ).val := fun τ => rfl
  have hψ₂_val : ∀ τ, ((ψ₂ τ : Fˣ) : F) = cast (cyc τ : ZMod p) := fun τ => rfl

  suffices hΦσ : Φ σ = 1 by
    rw [hΦ_apply, mul_inv_eq_one] at hΦσ
    have := congrArg (fun u : Fˣ => (u : F)) hΦσ
    simpa [hψ₁_val, hψ₂_val, Units.val_pow_eq_pow_val] using this

  have hopen : IsOpen ((Φ.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
    have h1 := isOpen_ker_of_galoisFactorsThroughFiniteLevel ρ hfin
    have h2 := MonoidHom.isOpen_ker_of_cycloCharSpec p cyc hcyc
    refine Subgroup.isOpen_mono (H₁ := ρ.ker ⊓ cyc.ker) ?_ ?_
    · intro τ hτ
      simp only [SetLike.mem_coe, Subgroup.mem_inf, MonoidHom.mem_ker] at hτ ⊢
      obtain ⟨hτ1, hτ2⟩ := hτ
      rw [hΦ_apply]
      have e1 : ψ₁ τ = 1 := by rw [hψ₁]; simp [hτ1]
      have e2 : ψ₂ τ = 1 := by rw [hψ₂]; simp [hτ2]
      rw [e1, e2, one_pow, inv_one, mul_one]
    · rw [Subgroup.coe_inf]; exact h1.inter h2

  set T : Finset ℕ := hSfin.toFinset.filter (· ≠ 0) with hT
  set M : ℕ := p * N * ∏ s ∈ T, s with hM
  have hMpos : 0 < M := by
    refine Nat.mul_pos (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero (NeZero.ne N))) ?_
    exact Finset.prod_pos fun s hs => Nat.pos_of_ne_zero (Finset.mem_filter.mp hs).2
  obtain ⟨ℓ, A, τ, g, n, hℓ, hℓM, hA, hτ, hmem⟩ :=
    Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen Φ.ker hopen σ hMpos

  have hpM : p ∣ M := by rw [hM]; exact dvd_mul_of_dvd_left (dvd_mul_right p N) _
  have hNM : N ∣ M := by rw [hM]; exact dvd_mul_of_dvd_left (dvd_mul_left N p) _
  have hTM : ∀ s ∈ T, s ∣ M := fun s hs => by
    rw [hM]; exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hs) _
  have hℓp : ¬ ℓ ∣ p := fun h => hℓM (h.trans hpM)
  have hℓnep : ℓ ≠ p := fun h => hℓp (h ▸ dvd_refl _)
  have hℓN : ¬ ℓ ∣ N := fun h => hℓM (h.trans hNM)
  have hℓS : ℓ ∉ S := by
    intro h
    have hℓT : ℓ ∈ T := Finset.mem_filter.mpr ⟨hSfin.mem_toFinset.mpr h, hℓ.ne_zero⟩
    exact hℓM (hTM ℓ hℓT)

  have hΦτ : Φ τ = 1 := by
    have hd : Matrix.det (ρ τ).val = (ℓ : F) ^ m := hdet ℓ hℓ hℓN hℓS hℓnep A hA τ hτ
    have hc : cyc τ = ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓp) :=
      ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt p cyc hcyc ℓ hℓ hℓp A hA τ hτ
    have hu : ψ₁ τ = (ψ₂ τ) ^ m := by
      ext
      rw [hψ₁_val, Units.val_pow_eq_pow_val, hψ₂_val, hd, hc, ZMod.coe_unitOfCoprime, map_natCast]
    rw [hΦ_apply, hu, mul_inv_cancel]

  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hΦτ, one_pow,
    mul_one, mul_inv_cancel, one_mul, inv_eq_one] at hmem
  exact hmem

end S_GaloisRep_det_eq_cycloChar_pow_of_det_frobenius_eq_pow
end P2MW
export P2MW.S_GaloisRep_det_eq_cycloChar_pow_of_det_frobenius_eq_pow (solution)
