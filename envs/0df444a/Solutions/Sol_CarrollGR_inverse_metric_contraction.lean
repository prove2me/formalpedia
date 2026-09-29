-- Prove2me | solution 1 for CarrollGR.inverse_metric_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T18:50:10.838997+00:00
-- url     : https://prove2.me/submissions/ee76b6ee-240b-470f-85c1-83b72d6cd937

import Mathlib
import Definitions.Def_CarrollGR_Defs

/-! 1868b9db CarrollGR.inverse_metric_contraction.
IsLorentzian M (Pᵀ M P = η, det P a unit) forces det M ≠ 0 (det η = -1) and M = Mᵀ
(transpose the congruence and cancel the invertible P, Pᵀ). Then Σ_{μν} M⁻¹_{μν} M_{μν}
= Σ_μ (M⁻¹ M)_{μμ} = tr 1 = 4. -/

set_option autoImplicit false

open scoped ContDiff

namespace CGRBuild

open CarrollGR Matrix

theorem lor_det_ne {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) : M.det ≠ 0 := by
  obtain ⟨P, _, h⟩ := hM
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  intro h0
  rw [h0] at h2
  simp [minkowskiEta, Matrix.det_diagonal, Fin.prod_univ_four] at h2

theorem lor_symm {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) : Mᵀ = M := by
  obtain ⟨P, hP, h⟩ := hM
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
  have hPtu : IsUnit Pᵀ := (Matrix.isUnit_iff_isUnit_det Pᵀ).mpr (by rw [Matrix.det_transpose]; exact hP)
  have ht : Pᵀ * Mᵀ * P = minkowskiEta := by
    have h' := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h'
    rw [Matrix.mul_assoc, h']
    simp [minkowskiEta, Matrix.diagonal_transpose]
  have e : Pᵀ * Mᵀ * P = Pᵀ * M * P := by rw [ht, h]
  exact hPtu.mul_left_cancel (hPu.mul_right_cancel e)

theorem lor_symm' {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) (a b : Fin 4) :
    M a b = M b a := by
  have h := congrFun (congrFun (lor_symm hM) b) a
  rw [Matrix.transpose_apply] at h
  exact h

theorem inv_contract {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : IsLorentzian M) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, M⁻¹ μ ν * M μ ν = 4 := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr (lor_det_ne hM)
  have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hu
  have e : ∀ μ, ∑ ν : Fin 4, M⁻¹ μ ν * M μ ν = (M⁻¹ * M) μ μ := by
    intro μ
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [lor_symm' hM μ ν]
  simp_rw [e, h1]
  simp [Fin.sum_univ_four, Matrix.one_apply]

end CGRBuild

open CarrollGR in open scoped ContDiff in
theorem solution (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : IsLorentzian M) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, M⁻¹ μ ν * M μ ν = 4 := by
  exact CGRBuild.inv_contract hM
