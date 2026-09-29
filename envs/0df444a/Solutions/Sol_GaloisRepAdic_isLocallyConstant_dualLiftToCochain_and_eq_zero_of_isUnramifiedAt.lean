-- Prove2me | solution 1 for GaloisRepAdic.isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/93b5ac08-ee39-5394-943f-126f6ceafa0b

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt

set_option autoImplicit false

open groupCohomology TrivSqZeroExt
open scoped Pointwise

namespace P2mK4NAdm

variable {k : Type} [Field k]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem maximalIdeal_dualNumber_sq :
    IsLocalRing.maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_bot, pow_two, DualNumber.eps_mul_eps]

theorem exists_level (ρA : GaloisRepAdic (DualNumber k)) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : Γℚ, (∀ x ∈ L, σ x = x) → ρA.ρ σ = 1 := by
  obtain ⟨L, hL, h⟩ := ρA.isAdicContinuous 2
  refine ⟨L, hL, fun σ hσ => ?_⟩
  apply LinearMap.ext
  intro v
  have := h σ hσ v
  rw [maximalIdeal_dualNumber_sq, Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] at this
  simpa using this

variable (ρbar : ResidualGaloisRep k) (ρA : GaloisRepAdic (DualNumber k))
  (ρd : Γℚ →* (DualNumber (Module.End k ρbar.V))ˣ)
  (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V)
  (hfr : ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩)

include hfr

theorem fst_eq_one_and_snd_eq_zero {σ : Γℚ} (h : ρA.ρ σ = 1) :
    (ρd σ : DualNumber (Module.End k ρbar.V)).fst = 1 ∧
      (ρd σ : DualNumber (Module.End k ρbar.V)).snd = 0 := by
  classical
  have hσ := hfr σ
  rw [h, LinearMap.toMatrix_one] at hσ
  have h2 := congrArg Matrix.dualNumberEquiv hσ
  rw [AlgEquiv.apply_symm_apply, map_one] at h2

  have hF : LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst) = 1 := by
    have := congrArg TrivSqZeroExt.fst h2
    rw [TrivSqZeroExt.fst_one] at this
    exact this.symm
  have hS : LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd) = 0 := by
    have := congrArg TrivSqZeroExt.snd h2
    rw [TrivSqZeroExt.snd_one] at this
    exact this.symm
  constructor
  · apply (LinearMap.toMatrix bbar bbar).injective
    rw [hF, LinearMap.toMatrix_one]
  · apply (LinearMap.toMatrix bbar bbar).injective
    rw [hS, map_zero]

theorem ρd_eq_one {σ : Γℚ} (h : ρA.ρ σ = 1) : ρd σ = 1 := by
  obtain ⟨h1, h2⟩ := fst_eq_one_and_snd_eq_zero ρbar ρA ρd b bbar hfr h
  apply Units.ext
  exact TrivSqZeroExt.ext h1 h2

theorem cochain_eq_zero {σ : Γℚ} (h : ρA.ρ σ = 1) :
    dualLiftToCochain ρbar.ρ.toHomUnits ρd σ = 0 := by
  unfold dualLiftToCochain
  rw [(fst_eq_one_and_snd_eq_zero ρbar ρA ρd b bbar hfr h).2, zero_mul]

theorem cochain_eq_zero_of_isUnramifiedAt (q : ℕ) (hq : ρA.IsUnramifiedAt q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : Γℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    dualLiftToCochain ρbar.ρ.toHomUnits ρd σ = 0 :=
  cochain_eq_zero ρbar ρA ρd b bbar hfr (hq P hP σ hσ)

theorem isLocallyConstant_cochain (hd : IsDualLift ρbar.ρ.toHomUnits ρd) :
    IsLocallyConstant (dualLiftToCochain ρbar.ρ.toHomUnits ρd) := by
  obtain ⟨L, hL, hlev⟩ := exists_level ρA
  haveI := hL
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨g • (L.fixingSubgroup : Set Γℚ), L.fixingSubgroup_isOpen.leftCoset g, ?_, ?_⟩
  · exact ⟨1, L.fixingSubgroup.one_mem, by simp⟩
  · rintro x ⟨s, hs, rfl⟩
    have hs' : ∀ x ∈ L, s x = x := (IntermediateField.mem_fixingSubgroup_iff L s).mp hs
    have hρA : ρA.ρ s = 1 := hlev s hs'
    have hρd : ρd s = 1 := ρd_eq_one ρbar ρA ρd b bbar hfr hρA
    have hfst := (fst_eq_one_and_snd_eq_zero ρbar ρA ρd b bbar hfr hρA).1
    have hρbar : ρbar.ρ.toHomUnits s = 1 := by
      have hval : ((ρbar.ρ.toHomUnits s : (Module.End k ρbar.V)ˣ) : Module.End k ρbar.V) = 1 := by
        rw [← hd s, hfst]
      exact Units.val_eq_one.mp hval
    change dualLiftToCochain ρbar.ρ.toHomUnits ρd (g * s) = dualLiftToCochain ρbar.ρ.toHomUnits ρd g
    unfold dualLiftToCochain
    rw [map_mul, map_mul, hρd, hρbar, mul_one, mul_one]

theorem level_props (hd : IsDualLift ρbar.ρ.toHomUnits ρd)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hlev : ∀ σ : Γℚ, (∀ x ∈ L, σ x = x) → ρA.ρ σ = 1) :
    (∀ σ : Γℚ, (∀ x ∈ L, σ x = x) → dualLiftToCochain ρbar.ρ.toHomUnits ρd σ = 0) ∧
    (∀ g s : Γℚ, (∀ x ∈ L, s x = x) →
      dualLiftToCochain ρbar.ρ.toHomUnits ρd (g * s) = dualLiftToCochain ρbar.ρ.toHomUnits ρd g) := by
  refine ⟨fun σ hσ => cochain_eq_zero ρbar ρA ρd b bbar hfr (hlev σ hσ), fun g s hs => ?_⟩
  have hρA : ρA.ρ s = 1 := hlev s hs
  have hρd : ρd s = 1 := ρd_eq_one ρbar ρA ρd b bbar hfr hρA
  have hfst := (fst_eq_one_and_snd_eq_zero ρbar ρA ρd b bbar hfr hρA).1
  have hρbar : ρbar.ρ.toHomUnits s = 1 := by
    have hval : ((ρbar.ρ.toHomUnits s : (Module.End k ρbar.V)ˣ) : Module.End k ρbar.V) = 1 := by
      rw [← hd s, hfst]
    exact Units.val_eq_one.mp hval
  unfold dualLiftToCochain
  rw [map_mul, map_mul, hρd, hρbar, mul_one, mul_one]

end P2mK4NAdm

theorem solution
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (ρA : GaloisRepAdic (DualNumber k))
    (ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hd : IsDualLift ρbar.ρ.toHomUnits ρd)
    (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V)
    (hfr : ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩) :
    IsLocallyConstant (dualLiftToCochain ρbar.ρ.toHomUnits ρd) ∧
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = x) →
        dualLiftToCochain ρbar.ρ.toHomUnits ρd σ = 0) ∧
      (∀ g s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, s x = x) →
        dualLiftToCochain ρbar.ρ.toHomUnits ρd (g * s) =
          dualLiftToCochain ρbar.ρ.toHomUnits ρd g)) ∧
    ∀ q : ℕ, ρA.IsUnramifiedAt q →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, dualLiftToCochain ρbar.ρ.toHomUnits ρd σ = 0 := by
  refine ⟨P2mK4NAdm.isLocallyConstant_cochain ρbar ρA ρd b bbar hfr hd, ?_,
    P2mK4NAdm.cochain_eq_zero_of_isUnramifiedAt ρbar ρA ρd b bbar hfr⟩
  obtain ⟨L, hL, hlev⟩ := P2mK4NAdm.exists_level ρA
  exact ⟨L, hL, P2mK4NAdm.level_props ρbar ρA ρd b bbar hfr hd L hlev⟩

end S_GaloisRepAdic_isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt
end P2MW
export P2MW.S_GaloisRepAdic_isLocallyConstant_dualLiftToCochain_and_eq_zero_of_isUnramifiedAt (solution)
