-- Prove2me | solution 1 for GaloisRepAdic.detIsCyclotomic_iff_forall_trace_dualLiftToCochain_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f2d69061-135b-5235-99e9-9c171a8ff240

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_detIsCyclotomic_iff_forall_trace_dualLiftToCochain_eq_zero

set_option autoImplicit false

open IsLocalRing groupCohomology TrivSqZeroExt
open scoped DualNumber

theorem solution
    (k : Type) [Field k] (ρbar : ResidualGaloisRep k)
    (p : ℕ) (hp : (p : k) = 0) (hp0 : 0 < p)
    (hdet : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
      LinearMap.det (ρbar.ρ σ) = (a : k))
    (ρ : GaloisRepAdic (DualNumber k))
    (ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hρd : IsDualLift ρbar.ρ.toHomUnits ρd)
    (b : Module.Basis (Fin 2) (DualNumber k) ρ.V) (bbar : Module.Basis (Fin 2) k ρbar.V)
    (hdict : ∀ σ, LinearMap.toMatrix b b (ρ.ρ σ) =
      Matrix.dualNumberEquiv.symm
        ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
          LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩) :
    ρ.DetIsCyclotomic p ↔
      ∀ σ, LinearMap.trace k ρbar.V (dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) = 0 := by
  classical

  have hdetf : ∀ σ, LinearMap.det (ρ.ρ σ) =
      inl (LinearMap.det (ρbar.ρ σ)) + inr (LinearMap.det (ρbar.ρ σ) *
        LinearMap.trace k ρbar.V (dualLiftToCochain ρbar.ρ.toHomUnits ρd σ)) := by
    intro σ
    have hfst : (ρd σ : DualNumber (Module.End k ρbar.V)).fst = ρbar.ρ σ := hρd σ
    have hsnd : (ρd σ : DualNumber (Module.End k ρbar.V)).snd =
        dualLiftToCochain ρbar.ρ.toHomUnits ρd σ * ρbar.ρ σ :=
      (Units.inv_mul_cancel_right _ (ρbar.ρ.toHomUnits σ)).symm
    rw [← LinearMap.det_toMatrix b, hdict σ, hfst, hsnd, LinearMap.toMatrix_mul,
      ← LinearMap.det_toMatrix bbar (ρbar.ρ σ), LinearMap.trace_eq_matrix_trace k bbar]
    generalize LinearMap.toMatrix bbar bbar (ρbar.ρ σ) = X
    generalize LinearMap.toMatrix bbar bbar (dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) = C
    rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
    simp only [Matrix.dualNumberEquiv_symm_apply, Matrix.of_apply]
    ext
    · simp
    · simp only [snd_sub, snd_add, DualNumber.snd_mul, fst_mk, snd_mk, snd_inl, snd_inr, zero_add,
        Matrix.mul_apply, Fin.sum_univ_two]
      ring

  have hpA : ((p : ℕ) : DualNumber k) = 0 := by
    rw [← inl_natCast, hp, inl_zero]
  have hspan : ∀ n : ℕ, 0 < n → Ideal.span {((p ^ n : ℕ) : DualNumber k)} = ⊥ := by
    intro n hn
    rw [Ideal.span_singleton_eq_bot, Nat.cast_pow, hpA, zero_pow hn.ne']

  have hexp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ a : ℕ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a := by
    haveI : NeZero p := ⟨hp0.ne'⟩
    intro σ
    refine ⟨(modularCyclotomicCharacter.toFun p σ.toRingEquiv).val, fun μ hμ => ?_⟩
    have h := modularCyclotomicCharacter.toFun_spec' σ.toRingEquiv (rootsOfUnity.mkOfPowEq μ hμ).2
    simpa using h

  have hunit : ∀ σ, IsUnit (LinearMap.det (ρbar.ρ σ)) := fun σ =>
    (ρbar.ρ.toHomUnits σ).isUnit.map LinearMap.det
  constructor
  · rintro ⟨-, H⟩ σ
    obtain ⟨a, ha⟩ := hexp σ
    have h1 := H 1 σ a (fun μ hμ => ha μ (by rwa [pow_one] at hμ))
    rw [hspan 1 one_pos, Ideal.mem_bot, sub_eq_zero, hdetf σ] at h1
    have h2 := congrArg TrivSqZeroExt.snd h1
    simp only [snd_add, snd_inl, snd_inr, zero_add, snd_natCast] at h2
    exact (mul_eq_zero.mp h2).resolve_left (hunit σ).ne_zero
  · intro htr
    refine ⟨by rw [hpA]; exact Ideal.zero_mem _, fun n σ a ha => ?_⟩
    cases n with
    | zero => simp
    | succ n =>
      have ha1 : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a := fun μ hμ =>
        ha μ (by rw [pow_succ', pow_mul, hμ, one_pow])
      rw [hspan (n + 1) n.succ_pos, Ideal.mem_bot, sub_eq_zero, hdetf σ, htr σ, mul_zero, inr_zero,
        add_zero, hdet σ a ha1, inl_natCast]

end S_GaloisRepAdic_detIsCyclotomic_iff_forall_trace_dualLiftToCochain_eq_zero
end P2MW
export P2MW.S_GaloisRepAdic_detIsCyclotomic_iff_forall_trace_dualLiftToCochain_eq_zero (solution)
