-- Prove2me | solution 1 for BoydADMM.ModelFit.lasso_x_update_ridge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:52:41.749989+00:00
-- url     : https://prove2.me/submissions/40833390-2cb5-40e4-804c-1be8c9851ad9

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

lemma gl_ridge_growth {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (z u : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin n))
    (hg : Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x0 - b) + ρ • (x0 - z + u) = 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * ‖Matrix.toEuclideanLin A y - b‖ ^ 2 + ρ / 2 * ‖y - z + u‖ ^ 2 =
      (1 / 2 * ‖Matrix.toEuclideanLin A x0 - b‖ ^ 2 + ρ / 2 * ‖x0 - z + u‖ ^ 2) +
        1 / 2 * ‖Matrix.toEuclideanLin A (y - x0)‖ ^ 2 + ρ / 2 * ‖y - x0‖ ^ 2 := by
  have e1 : Matrix.toEuclideanLin A y - b =
      (Matrix.toEuclideanLin A x0 - b) + Matrix.toEuclideanLin A (y - x0) := by
    rw [map_sub]; abel
  have e2 : y - z + u = (x0 - z + u) + (y - x0) := by abel
  rw [e1, e2, norm_add_sq_real, norm_add_sq_real,
    real_inner_comm (Matrix.toEuclideanLin A (y - x0)), gl_inner_tel]
  have h0 : inner ℝ (Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x0 - b) +
      ρ • (x0 - z + u)) (y - x0) = 0 := by rw [hg, inner_zero_left]
  rw [inner_add_left, inner_smul_left] at h0
  simp only [conj_trivial] at h0
  have k := real_inner_comm (y - x0) (Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x0 - b))
  linarith

theorem lasso_x_update_ridge_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (z u : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ)
    (x : EuclideanSpace ℝ (Fin n)) :
    IsMinOn (fun x' : EuclideanSpace ℝ (Fin n) =>
        1 / 2 * ‖Matrix.toEuclideanLin A x' - b‖ ^ 2 + ρ / 2 * ‖x' - z + u‖ ^ 2) Set.univ x ↔
      x = Matrix.toEuclideanLin ((Aᵀ * A + ρ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)
        (Matrix.toEuclideanLin Aᵀ b + ρ • (z - u)) := by
  set x0 := Matrix.toEuclideanLin ((Aᵀ * A + ρ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)
        (Matrix.toEuclideanLin Aᵀ b + ρ • (z - u)) with hx0
  have hP : Matrix.toEuclideanLin (Aᵀ * A + ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) x0 =
      Matrix.toEuclideanLin Aᵀ b + ρ • (z - u) := by
    rw [hx0, gl_tel_tel, (gl_inv_mul A ρ hρ).2]; simp
  have hg : Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x0 - b) + ρ • (x0 - z + u) = 0 := by
    rw [gl_tel_ridge, ← gl_tel_tel] at hP
    rw [map_sub, smul_add, smul_sub]
    rw [smul_sub] at hP
    have : Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x0) + ρ • x0 - (Matrix.toEuclideanLin Aᵀ b + (ρ • z - ρ • u)) = 0 := by
      rw [hP]; abel
    rw [← this]; abel
  apply gl_unique_of_growth _ x0 (ρ / 2) (by linarith)
  intro y
  rw [gl_ridge_growth A b z u ρ x0 hg y]
  nlinarith [sq_nonneg ‖Matrix.toEuclideanLin A (y - x0)‖]

end BoydADMM.ModelFit

open BoydADMM.ModelFit


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (z u : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ)
    (x : EuclideanSpace ℝ (Fin n)) :
    IsMinOn (fun x' : EuclideanSpace ℝ (Fin n) =>
        1 / 2 * ‖Matrix.toEuclideanLin A x' - b‖ ^ 2 + ρ / 2 * ‖x' - z + u‖ ^ 2) Set.univ x ↔
      x = Matrix.toEuclideanLin ((Aᵀ * A + ρ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)
        (Matrix.toEuclideanLin Aᵀ b + ρ • (z - u)) := by
  exact lasso_x_update_ridge_core A b z u ρ hρ x
