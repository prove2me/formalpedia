-- Prove2me | solution 1 for GaussianMatrix.schur_offdiag_inv
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:37:02.700698+00:00
-- url     : https://prove2.me/submissions/87e5087c-68ee-48b4-b358-88f510f3396a

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma schur_offdiag_inv_aux {n k : ℕ} (G : Matrix (Fin (n + 1)) (Fin k) ℝ) (i : Fin (n + 1))
    (a : Fin n)
    (hH : (G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ).det ≠ 0) :
    (G * Gᵀ)⁻¹ i (i.succAbove a) =
      -(((G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ)⁻¹ *ᵥ
          (G.submatrix i.succAbove id *ᵥ G i)) a) * (G * Gᵀ)⁻¹ i i := by
  set H : Matrix (Fin n) (Fin k) ℝ := G.submatrix i.succAbove id with hHdef
  set g : Fin k → ℝ := G i with hg
  set M : Matrix (Fin n) (Fin n) ℝ := H * Hᵀ with hM
  set c : Fin n → ℝ := M⁻¹ *ᵥ (H *ᵥ g) with hc
  set s : ℝ := g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ c with hs
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := G * Gᵀ with hA
  set w : Fin k → ℝ := g - Hᵀ *ᵥ c with hw
  set x : Fin (n + 1) → ℝ := Fin.insertNth i (1 : ℝ) (-c) with hx
  have hHw : H *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← hM, hc, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH), Matrix.one_mulVec, sub_self]
  have hgw : g ⬝ᵥ w = s := by
    rw [hw, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hGx : Gᵀ *ᵥ x = w := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hw, hx, Pi.sub_apply, hg,
      hHdef, Matrix.submatrix_apply, id]
    rw [Fin.sum_univ_succAbove _ i]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib]
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
  have hadj : A.adjugate i i = M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have : A.submatrix i.succAbove i.succAbove = M := by
      ext a b
      simp [hA, hM, hHdef, Matrix.mul_apply]
    rw [this, ← two_mul, pow_mul]
    norm_num
  have hdetA : A.det = s * M.det := by
    have h1 : A.adjugate *ᵥ (A *ᵥ x) = A.det • x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hAx] at h1
    have h2 := congrFun h1 i
    have h3 : (A.adjugate *ᵥ Pi.single i s) i = A.adjugate i i * s := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h3, Pi.smul_apply, smul_eq_mul, hx, Fin.insertNth_apply_same, mul_one, hadj] at h2
    rw [← h2, mul_comm]
  -- symmetry of `A⁻¹`
  have hAt : Aᵀ = A := by rw [hA, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hsymm : A⁻¹ i (i.succAbove a) = A⁻¹ (i.succAbove a) i := by
    have : (A⁻¹)ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hAt]
    rw [← this, Matrix.transpose_apply, this]
  by_cases hs0 : s = 0
  · -- singular case: both sides vanish
    have hA0 : A⁻¹ = 0 := by
      apply Matrix.nonsing_inv_apply_not_isUnit
      rw [hdetA, hs0, zero_mul]; exact not_isUnit_zero
    show A⁻¹ i (i.succAbove a) = -c a * A⁻¹ i i
    rw [hA0]; simp
  · have hdetU : IsUnit A.det := by
      rw [hdetA]; exact isUnit_iff_ne_zero.mpr (mul_ne_zero hs0 hH)
    -- `A⁻¹ eᵢ = x / s`
    have hcol : A⁻¹ *ᵥ Pi.single i s = x := by
      rw [← hAx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetU, Matrix.one_mulVec]
    have hcol' : ∀ b, A⁻¹ b i * s = x b := by
      intro b
      have := congrFun hcol b
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    have hii : A⁻¹ i i * s = 1 := by
      rw [hcol' i, hx, Fin.insertNth_apply_same]
    have hai : A⁻¹ (i.succAbove a) i * s = -c a := by
      rw [hcol' (i.succAbove a), hx, Fin.insertNth_apply_succAbove, Pi.neg_apply]
    show A⁻¹ i (i.succAbove a) = -c a * A⁻¹ i i
    rw [hsymm]
    have hsinv : A⁻¹ i i = s⁻¹ := by
      field_simp; linarith
    rw [hsinv]
    field_simp
    linarith

end GaussianMatrix

open GaussianMatrix

theorem solution {n k : ℕ} (G : Matrix (Fin (n + 1)) (Fin k) ℝ) (i : Fin (n + 1))
    (a : Fin n)
    (hH : (G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ).det ≠ 0) :
    (G * Gᵀ)⁻¹ i (i.succAbove a) =
      -(((G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ)⁻¹ *ᵥ
          (G.submatrix i.succAbove id *ᵥ G i)) a) * (G * Gᵀ)⁻¹ i i :=
  schur_offdiag_inv_aux G i a hH
