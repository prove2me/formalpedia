-- Prove2me | solution 1 for CerednikDrinfeld.SpecialModule.exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a68c5500-bda7-5d43-a81a-1d8d66d39f44

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_span_eq_top_forall_exists_algHom_of_isAlgClosed
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two_of_charZero
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_Module_End_exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialModule_exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (k : Type) [Field k] [IsAlgClosed k] (hqq : IsUnit ((q * q' : ℕ) : k))
    (W : Type) [AddCommGroup W] [Module k W] [Module.Finite k W] (hW : Module.finrank k W = 2)
    (Ψ : ↥Λ → (W →ₗ[k] W))
    (hΨ_add : ∀ x y : ↥Λ, Ψ (x + y) = Ψ x + Ψ y)
    (hΨ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, Ψ ⟨1, h1⟩ = LinearMap.id)
    (hΨ_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      Ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = Ψ x ∘ₗ Ψ y) :
    ∃ (θ : ↥Λ → Matrix (Fin 2) (Fin 2) k) (e : W ≃ₗ[k] (Fin 2 → k)),
      (∀ (x : ↥Λ) (w : W), e (Ψ x w) = (θ x).mulVec (e w)) ∧
      (∀ x y : ↥Λ, θ (x + y) = θ x + θ y) ∧
      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, θ ⟨1, h1⟩ = 1) ∧
      (∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        θ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = θ x * θ y) ∧
      (∀ m : Matrix (Fin 2) (Fin 2) k, m ∈ Submodule.span k (Set.range θ)) ∧
      (∀ x : ↥Λ, θ (star x) = (θ μ)⁻¹ * (θ x).adjugate * θ μ) ∧
      (θ μ).trace = 0 ∧ (θ μ).det = ((q * q' : ℕ) : k) ∧
      (∀ (x : ↥Λ) (n : ℤ), (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        (θ x).trace = (n : k)) := by
  classical
  have hO := hΛ.isOrder

  obtain ⟨φ, hφ1, hφmul, hφspan, hφuniv⟩ := QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_span_eq_top_forall_exists_algHom_of_isAlgClosed hB Λ hΛ k hqq

  let ρ : ↥Λ →ₗ[ℤ] (W →ₗ[k] W) := (AddMonoidHom.mk' Ψ hΨ_add).toIntLinearMap
  have hρ : ∀ x, ρ x = Ψ x := fun _ => rfl
  obtain ⟨ψ, hψ⟩ := hφuniv (W →ₗ[k] W) ρ
    (fun h1 => by rw [hρ, hΨ_one h1]; rfl)
    (fun x y hxy => by rw [hρ, hρ, hρ, hΨ_mul x y hxy]; rfl)

  obtain ⟨e, he⟩ := Module.End.exists_linearEquiv_forall_algHom_matrix_apply_eq_mulVec_of_finrank_eq_two k W hW ψ
  have heΨ : ∀ (x : ↥Λ) (w : W), e (Ψ x w) = (φ x).mulVec (e w) := by
    intro x w; rw [← hρ x, ← hψ x, he]

  have hq0 : (q : k) ≠ 0 := by
    intro h; apply hqq.ne_zero; push_cast; rw [h, zero_mul]
  have hq'0 : (q' : k) ≠ 0 := by
    intro h; apply hqq.ne_zero; push_cast; rw [h, mul_zero]
  have htraceΨ : ∀ (x : ↥Λ) (n : ℤ), (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      LinearMap.trace k W (Ψ x) = (n : k) := by
    intro x n hn
    obtain ⟨p, hp⟩ := CharP.exists k
    rcases CharP.char_is_prime_or_zero k p with hprime | h0
    · haveI : Fact p.Prime := ⟨hprime⟩
      have hpq : p ≠ q := by
        rintro rfl; exact hq0 (CharP.cast_eq_zero k p)
      have hpq' : p ≠ q' := by
        rintro rfl; exact hq'0 (CharP.cast_eq_zero k p)
      exact QuaternionAlgebra.IsMaximalOrder.trace_eq_intCast_of_add_star_eq_of_finrank_eq_two hB hΛ hpq hpq' hW Ψ hΨ_add (fun h1 => by rw [hΨ_one h1]; rfl) (fun x y hxy => by rw [hΨ_mul x y hxy]; rfl) x n hn
    · subst h0
      haveI : CharZero k := CharP.charP_to_charZero k
      exact QuaternionAlgebra.IsMaximalOrder.trace_eq_intCast_of_add_star_eq_of_finrank_eq_two_of_charZero hB hΛ hW Ψ hΨ_add (fun h1 => by rw [hΨ_one h1]; rfl) (fun x y hxy => by rw [hΨ_mul x y hxy]; rfl) x n hn

  have hconj : ∀ x : ↥Λ, Ψ x = (e.symm.toLinearMap ∘ₗ Matrix.toLin' (φ x)) ∘ₗ e.toLinearMap := by
    intro x; apply LinearMap.ext; intro w
    apply e.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, Matrix.toLin'_apply, heΨ]
  have htrace : ∀ x : ↥Λ, (φ x).trace = LinearMap.trace k W (Ψ x) := by
    intro x
    rw [hconj, LinearMap.trace_comp_comm']
    have hee : e.toLinearMap ∘ₗ (e.symm.toLinearMap ∘ₗ Matrix.toLin' (φ x)) = Matrix.toLin' (φ x) := by
      apply LinearMap.ext; intro v; simp
    rw [hee, LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
  have htr : ∀ (x : ↥Λ) (n : ℤ), (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      (φ x).trace = (n : k) := fun x n hn => by rw [htrace]; exact htraceΨ x n hn

  have hre : (μ : ℍ[ℚ, a, b]).re = 0 := by
    have hI := congrArg QuaternionAlgebra.imI hμ
    have hJ := congrArg QuaternionAlgebra.imJ hμ
    have hK := congrArg QuaternionAlgebra.imK hμ
    have hR := congrArg QuaternionAlgebra.re hμ
    simp at hI hJ hK hR
    by_contra hne
    have hi : (μ : ℍ[ℚ, a, b]).imI = 0 := by
      have h2 : (μ : ℍ[ℚ, a, b]).re * (μ : ℍ[ℚ, a, b]).imI = 0 := by linear_combination hI / 2
      exact (mul_eq_zero.1 h2).resolve_left hne
    have hj : (μ : ℍ[ℚ, a, b]).imJ = 0 := by
      have h2 : (μ : ℍ[ℚ, a, b]).re * (μ : ℍ[ℚ, a, b]).imJ = 0 := by linear_combination hJ / 2
      exact (mul_eq_zero.1 h2).resolve_left hne
    have hk' : (μ : ℍ[ℚ, a, b]).imK = 0 := by
      have h2 : (μ : ℍ[ℚ, a, b]).re * (μ : ℍ[ℚ, a, b]).imK = 0 := by linear_combination hK / 2
      exact (mul_eq_zero.1 h2).resolve_left hne
    rw [hi, hj, hk'] at hR
    have hpos : (0 : ℚ) < (q : ℚ) * (q' : ℚ) := by
      have := (Fact.out : q.Prime).pos; have := (Fact.out : q'.Prime).pos; positivity
    nlinarith [sq_nonneg ((μ : ℍ[ℚ, a, b]).re)]
  have hμsum : (μ : ℍ[ℚ, a, b]) + Star.star (μ : ℍ[ℚ, a, b]) = (((0 : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [QuaternionAlgebra.add_star_eq_coe_trd, QuaternionAlgebra.trd, hre]; simp
  have htrμ : (φ μ).trace = 0 := by have h := htr μ 0 hμsum; simpa using h

  have hμμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem μ.2 μ.2
  have hcoe1 : ∀ z : ℤ, ((z : ℚ) : ℍ[ℚ, a, b]) = ((z • (⟨1, hO.one_mem⟩ : ↥Λ) : ↥Λ) : ℍ[ℚ, a, b]) := by
    intro z; rw [Submodule.coe_smul, zsmul_eq_mul, mul_one]; norm_cast
  have hφz : ∀ z : ℤ, φ (z • ⟨1, hO.one_mem⟩) = (z : k) • (1 : Matrix (Fin 2) (Fin 2) k) := by
    intro z; rw [map_zsmul, hφ1, ← Int.cast_smul_eq_zsmul k]
  have hel : (⟨(μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]), hμμ⟩ : ↥Λ) = (-(q * q' : ℤ)) • ⟨1, hO.one_mem⟩ := by
    apply Subtype.ext
    change (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = (((-(q * q' : ℤ)) • (⟨1, hO.one_mem⟩ : ↥Λ) : ↥Λ) : ℍ[ℚ, a, b])
    rw [← hcoe1, hμ, Algebra.smul_def, mul_one]
    norm_cast
  have hMM : φ μ * φ μ = (((-(q * q' : ℤ)) : ℤ) : k) • (1 : Matrix (Fin 2) (Fin 2) k) := by
    rw [← hφmul μ μ hμμ, ← hφz, hel]
  have h00 := congrFun (congrFun hMM 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  have htr2 := htrμ
  rw [Matrix.trace_fin_two] at htr2
  have hdet : (φ μ).det = ((q * q' : ℕ) : k) := by
    rw [Matrix.det_fin_two]
    push_cast at h00 ⊢
    linear_combination (φ μ 0 0) * htr2 - h00
  have hdetu : IsUnit (φ μ).det := by rw [hdet]; exact hqq

  have hstarθ : ∀ x : ↥Λ, φ (star x) = (φ μ)⁻¹ * (φ x).adjugate * φ μ := by
    intro x
    obtain ⟨-, t, ht⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO x.2
    have hxs : (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]) := by
      rw [QuaternionAlgebra.add_star_eq_coe_trd, ← ht]
    have htrx : (φ x).trace = (t : k) := htr x t hxs
    have hbar : Star.star (x : ℍ[ℚ, a, b]) = ((t • (⟨1, hO.one_mem⟩ : ↥Λ) - x : ↥Λ) : ℍ[ℚ, a, b]) := by
      rw [Submodule.coe_sub, ← hcoe1, ← hxs]; abel
    have hbar_mem : Star.star (x : ℍ[ℚ, a, b]) ∈ Λ := by rw [hbar]; exact (t • (⟨1, hO.one_mem⟩ : ↥Λ) - x).2
    have hφxb : φ ⟨Star.star (x : ℍ[ℚ, a, b]), hbar_mem⟩ = (φ x).adjugate := by
      have hel : (⟨Star.star (x : ℍ[ℚ, a, b]), hbar_mem⟩ : ↥Λ) = t • ⟨1, hO.one_mem⟩ - x := Subtype.ext hbar
      rw [hel, map_sub, hφz, Matrix.adjugate_fin_two]
      rw [Matrix.trace_fin_two] at htrx
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply] <;> linear_combination (-1 : k) * htrx
    have h1 : φ μ * φ (star x) = (φ x).adjugate * φ μ := by
      rw [← hφxb, ← hφmul μ (star x) (hO.mul_mem μ.2 (star x).2), ← hφmul _ μ (hO.mul_mem hbar_mem μ.2)]
      congr 1; exact Subtype.ext (hstar x)
    calc φ (star x) = ((φ μ)⁻¹ * φ μ) * φ (star x) := by rw [Matrix.nonsing_inv_mul _ hdetu, one_mul]
      _ = (φ μ)⁻¹ * ((φ x).adjugate * φ μ) := by rw [mul_assoc, h1]
      _ = (φ μ)⁻¹ * (φ x).adjugate * φ μ := by rw [mul_assoc]
  exact ⟨fun x => φ x, e, heΨ, fun x y => map_add φ x y, hφ1, hφmul, fun m => hφspan ▸ Submodule.mem_top,
    hstarθ, htrμ, hdet, htr⟩

end S_CerednikDrinfeld_SpecialModule_exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialModule_exists_matrix_linearEquiv_forall_mulVec_of_finrank_eq_two_of_isUnit (solution)
