-- Prove2me | solution 1 for BoydADMM.ModelFit.group_lasso_eigen_norm
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:05:32.16122+00:00
-- url     : https://prove2.me/submissions/23b5739f-13bf-4e1a-9d6c-2d2c65b24225

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix


namespace BoydADMM.ModelFit

lemma gl_tel_tel {m n k : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    Matrix.toEuclideanLin M (Matrix.toEuclideanLin N x) = Matrix.toEuclideanLin (M * N) x := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

lemma gl_inner_tel {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (Matrix.toEuclideanLin A x) y = inner ℝ x (Matrix.toEuclideanLin Aᵀ y) := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [conjTranspose_eq_transpose_of_trivial] at h
  rw [h, LinearMap.adjoint_inner_right]

lemma gl_tel_ridge {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (ν : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (P + ν • (1 : Matrix (Fin n) (Fin n) ℝ)) x =
      Matrix.toEuclideanLin P x + ν • x := by
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  simp

lemma gl_posDef {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ) (hν : 0 < ν) :
    (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have h1 : (Aᵀ * A).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self A
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  exact Matrix.PosDef.posSemidef_add h1 (Matrix.PosDef.one.smul hν)

lemma gl_inv_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ) (hν : 0 < ν) :
    (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ * (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 ∧
    (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)) * (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = 1 := by
  have hd : IsUnit (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (gl_posDef A ν hν).isUnit
  exact ⟨Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

lemma gl_unique_of_growth {E : Type*} [NormedAddCommGroup E] (f : E → ℝ) (x0 : E) (c : ℝ)
    (hc : 0 < c) (hg : ∀ y, f x0 + c * ‖y - x0‖ ^ 2 ≤ f y) (x : E) :
    IsMinOn f Set.univ x ↔ x = x0 := by
  rw [isMinOn_iff]
  constructor
  · intro hx
    have h1 := hx x0 (Set.mem_univ x0)
    have h2 := hg x
    have h3 : c * ‖x - x0‖ ^ 2 ≤ 0 := by linarith
    have h4 : ‖x - x0‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖x - x0‖]) (sq_nonneg _)
    have : ‖x - x0‖ = 0 := by simpa using h4
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · rintro rfl y _
    have := hg y
    nlinarith [sq_nonneg ‖y - x‖]

lemma gl_orth_norm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    (y : EuclideanSpace ℝ (Fin n)) : ‖Matrix.toEuclideanLin Q y‖ = ‖y‖ := by
  have h : ‖Matrix.toEuclideanLin Q y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, gl_inner_tel, gl_tel_tel,
      hQ, real_inner_comm]
    simp
  have := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

theorem eigen_norm_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (μ : Fin n → ℝ)
    (hdecomp : Aᵀ * A = Q * Matrix.diagonal μ * Qᵀ) (ν : ℝ) (hν : 0 < ν) :
    ‖ridgeSol A ν v‖ =
      ‖Matrix.toEuclideanLin ((Matrix.diagonal (fun j => μ j + ν))⁻¹ * Qᵀ * Aᵀ) v‖ := by
  have hQ1 : Qᵀ * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hQ
  have hQ2 : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hQ
  -- μ ≥ 0
  have hD : Matrix.diagonal μ = (A * Q)ᵀ * (A * Q) := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hdecomp]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᵀ Q, hQ1, Matrix.one_mul, Matrix.mul_one]
  have hμ : ∀ j, 0 ≤ μ j := by
    have hp : (Matrix.diagonal μ).PosSemidef := by
      rw [hD]
      have := Matrix.posSemidef_conjTranspose_mul_self (A * Q)
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    intro j
    have := hp.diag_nonneg (i := j)
    simpa using this
  set D' := Matrix.diagonal (fun j => μ j + ν) with hD'
  have hM : Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ) = Q * D' * Qᵀ := by
    rw [hdecomp, hD']
    have : Matrix.diagonal (fun j => μ j + ν) = Matrix.diagonal μ + ν • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ2]
  have hdet : IsUnit D'.det := by
    rw [hD', Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr (fun j _ => by linarith [hμ j] : ∀ j ∈ Finset.univ, μ j + ν ≠ 0)).isUnit
  have hinv : (Q * D' * Qᵀ)⁻¹ = Q * D'⁻¹ * Qᵀ := by
    apply Matrix.inv_eq_left_inv
    calc Q * D'⁻¹ * Qᵀ * (Q * D' * Qᵀ) = Q * (D'⁻¹ * (Qᵀ * Q) * D') * Qᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, hQ2]
  rw [ridgeSol, hM, hinv]
  rw [show Q * D'⁻¹ * Qᵀ * Aᵀ = Q * (D'⁻¹ * Qᵀ * Aᵀ) by simp only [Matrix.mul_assoc]]
  rw [← gl_tel_tel, gl_orth_norm Q hQ1]

end BoydADMM.ModelFit

open BoydADMM.ModelFit


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin n) ℝ) (μ : Fin n → ℝ)
    (hdecomp : Aᵀ * A = Q * Matrix.diagonal μ * Qᵀ) (ν : ℝ) (hν : 0 < ν) :
    ‖ridgeSol A ν v‖ =
      ‖Matrix.toEuclideanLin ((Matrix.diagonal (fun j => μ j + ν))⁻¹ * Qᵀ * Aᵀ) v‖ := by
  exact eigen_norm_core A v Q hQ μ hdecomp ν hν
