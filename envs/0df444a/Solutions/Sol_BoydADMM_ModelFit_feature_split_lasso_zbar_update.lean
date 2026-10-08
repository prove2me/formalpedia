-- Prove2me | solution 1 for BoydADMM.ModelFit.feature_split_lasso_zbar_update
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:54:09.956976+00:00
-- url     : https://prove2.me/submissions/dc97b35c-ba52-464f-a28d-70d70da16d6a

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

theorem fs_zbar_core {N m : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (b Axbar u zb : EuclideanSpace ℝ (Fin m)) :
    IsMinOn (fun z : EuclideanSpace ℝ (Fin m) =>
        1 / 2 * ‖(N : ℝ) • z - b‖ ^ 2 + (N : ℝ) * ρ / 2 * ‖z - Axbar - u‖ ^ 2) Set.univ zb ↔
      zb = (1 / ((N : ℝ) + ρ)) • (b + ρ • Axbar + ρ • u) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set z0 := (1 / ((N : ℝ) + ρ)) • (b + ρ • Axbar + ρ • u) with hz0
  have hk : ((N : ℝ) + ρ) • z0 = b + ρ • Axbar + ρ • u := by
    rw [hz0, smul_smul, mul_one_div_cancel (by linarith), one_smul]
  have hg : ((N : ℝ) • z0 - b) + ρ • (z0 - Axbar - u) = 0 := by
    have : ((N : ℝ) • z0 - b) + ρ • (z0 - Axbar - u) = ((N : ℝ) + ρ) • z0 - (b + ρ • Axbar + ρ • u) := by
      rw [add_smul, smul_sub, smul_sub]; abel
    rw [this, hk, sub_self]
  apply gl_unique_of_growth _ z0 (((N : ℝ) ^ 2 + N * ρ) / 2) (by positivity)
  intro y
  have e1 : (N : ℝ) • y - b = ((N : ℝ) • z0 - b) + (N : ℝ) • (y - z0) := by
    rw [smul_sub]; abel
  have e2 : y - Axbar - u = (z0 - Axbar - u) + (y - z0) := by abel
  have h0 : inner ℝ (((N : ℝ) • z0 - b) + ρ • (z0 - Axbar - u)) (y - z0) = 0 := by
    rw [hg, inner_zero_left]
  rw [inner_add_left, inner_smul_left] at h0
  simp only [conj_trivial] at h0
  rw [e1, e2, norm_add_sq_real, norm_add_sq_real, inner_smul_right, norm_smul,
    Real.norm_of_nonneg hN'.le]
  nlinarith [sq_nonneg ‖y - z0‖]

end BoydADMM.ModelFit

open BoydADMM.ModelFit


theorem solution {N m : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (b Axbar u zb : EuclideanSpace ℝ (Fin m)) :
    IsMinOn (fun z : EuclideanSpace ℝ (Fin m) =>
        1 / 2 * ‖(N : ℝ) • z - b‖ ^ 2 + (N : ℝ) * ρ / 2 * ‖z - Axbar - u‖ ^ 2) Set.univ zb ↔
      zb = (1 / ((N : ℝ) + ρ)) • (b + ρ • Axbar + ρ • u) := by
  exact fs_zbar_core hN ρ hρ b Axbar u zb
