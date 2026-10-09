-- Prove2me | solution 1 for GaussianMatrix.schur_diag_inv
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:48:21.742693+00:00
-- url     : https://prove2.me/submissions/e8e31e6b-c097-46bd-b9eb-3754bc9e51ff

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma schur_diag_inv_aux {n k : ℕ} (G : Matrix (Fin (n + 1)) (Fin k) ℝ) (i : Fin (n + 1))
    (hH : (G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ).det ≠ 0) :
    (G * Gᵀ)⁻¹ i i =
      (G i ⬝ᵥ G i - (G.submatrix i.succAbove id *ᵥ G i) ⬝ᵥ
        ((G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ)⁻¹ *ᵥ
          (G.submatrix i.succAbove id *ᵥ G i)))⁻¹ := by
  set H : Matrix (Fin n) (Fin k) ℝ := G.submatrix i.succAbove id with hHdef
  set g : Fin k → ℝ := G i with hg
  set M : Matrix (Fin n) (Fin n) ℝ := H * Hᵀ with hM
  set c : Fin n → ℝ := M⁻¹ *ᵥ (H *ᵥ g) with hc
  set s : ℝ := g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ c with hs
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := G * Gᵀ with hA
  set w : Fin k → ℝ := g - Hᵀ *ᵥ c with hw
  set x : Fin (n + 1) → ℝ := Fin.insertNth i (1 : ℝ) (-c) with hx
  -- residual is orthogonal to the other rows
  have hHw : H *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← hM, hc, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH), Matrix.one_mulVec, sub_self]
  have hgw : g ⬝ᵥ w = s := by
    rw [hw, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  -- Gᵀ x = w
  have hGx : Gᵀ *ᵥ x = w := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hw, hx, Pi.sub_apply, hg,
      hHdef, Matrix.submatrix_apply, id]
    rw [Fin.sum_univ_succAbove _ i]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib]
  -- G w = s e_i
  have hGw : G *ᵥ w = Pi.single i s := by
    funext b
    induction b using Fin.succAboveCases i with
    | x =>
      simp only [Pi.single_eq_same]
      rw [← hgw]; rfl
    | p a =>
      rw [Pi.single_eq_of_ne (Fin.succAbove_ne i a)]
      have := congrFun hHw a
      simpa [Matrix.mulVec, hHdef] using this
  have hAx : A *ᵥ x = Pi.single i s := by
    rw [hA, ← Matrix.mulVec_mulVec, hGx, hGw]
  -- the adjugate diagonal entry is det M
  have hadj : A.adjugate i i = M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have : A.submatrix i.succAbove i.succAbove = M := by
      ext a b
      simp [hA, hM, hHdef, Matrix.mul_apply]
    rw [this, ← two_mul, pow_mul]
    norm_num
  -- det A = s * det M
  have hdetA : A.det = s * M.det := by
    have h1 : A.adjugate *ᵥ (A *ᵥ x) = A.det • x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hAx] at h1
    have h2 := congrFun h1 i
    have h3 : (A.adjugate *ᵥ Pi.single i s) i = A.adjugate i i * s := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h3, Pi.smul_apply, smul_eq_mul, hx, Fin.insertNth_apply_same, mul_one, hadj] at h2
    rw [← h2, mul_comm]
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', hdetA, hadj,
    mul_inv, mul_assoc, inv_mul_cancel₀ hH, mul_one]

end GaussianMatrix

open GaussianMatrix

theorem solution {n k : ℕ} (G : Matrix (Fin (n + 1)) (Fin k) ℝ) (i : Fin (n + 1))
    (hH : (G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ).det ≠ 0) :
    (G * Gᵀ)⁻¹ i i =
      (G i ⬝ᵥ G i - (G.submatrix i.succAbove id *ᵥ G i) ⬝ᵥ
        ((G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ)⁻¹ *ᵥ
          (G.submatrix i.succAbove id *ᵥ G i)))⁻¹ :=
  schur_diag_inv_aux G i hH
