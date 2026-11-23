-- Prove2me | solution 1 for Bl.DetMonotoneStarMulSelf.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:57.697828+00:00
-- url     : https://prove2.me/submissions/c621d279-948d-4ac3-896d-c1d34273f265

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_Lemmata_DetMonotoneStarMulSelf_OneLeReDetOneAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.DetMonotoneStarMulSelf
open Matrix in
open scoped ComplexOrder in
private lemma one_le_re_det_one_add {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.PosSemidef) :
    1 ≤ (1 + D).det.re := by
  have hH : (1 + D).IsHermitian := isHermitian_one.add hD.isHermitian
  have key : ∀ i, 1 ≤ hH.eigenvalues i := by
    intro i
    rw [hH.eigenvalues_eq i]
    have h1 : RCLike.re (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i)) = (1 : ℝ) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hH.eigenvectorBasis.orthonormal.1 i]
      simp
    have h2 := hD.dotProduct_mulVec_nonneg (⇑(hH.eigenvectorBasis i))
    have h3 : 0 ≤ RCLike.re (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ D *ᵥ ⇑(hH.eigenvectorBasis i)) :=
      (Complex.nonneg_iff.mp h2).1
    rw [add_mulVec, one_mulVec, dotProduct_add, map_add, h1]
    linarith
  rw [hH.det_eq_prod_eigenvalues]
  have hp : (∏ i, ((hH.eigenvalues i : ℝ) : ℂ)).re = ∏ i, hH.eigenvalues i := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  refine le_of_le_of_eq ?_ hp.symm
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ ∏ i, hH.eigenvalues i := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => key i)
open Matrix in
open scoped ComplexOrder in
open scoped MatrixOrder in
private lemma exists_star_mul_self {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, B = Xᴴ * X := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  exact ⟨X, by rw [hX, star_eq_conjTranspose]⟩
open Matrix in
open scoped ComplexOrder in
private lemma det_mono {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef)
    (hAB : (A - B).PosSemidef) : B.det.re ≤ A.det.re := by
  have hA : A.PosSemidef := by simpa using hB.add hAB
  by_cases hdet : B.det = 0
  · rw [hdet, Complex.zero_re]
    exact (Complex.nonneg_iff.mp hA.det_nonneg).1
  · obtain ⟨X, hBX⟩ := exists_star_mul_self B hB
    have hXd : X.det ≠ 0 := by
      intro h
      apply hdet
      rw [hBX, det_mul, h, mul_zero]
    have hXu : IsUnit X.det := isUnit_iff_ne_zero.mpr hXd
    have hYX : X⁻¹ * X = 1 := nonsing_inv_mul X hXu
    set C := A - B with hCdef
    set D := (X⁻¹)ᴴ * C * X⁻¹ with hDdef
    have hD : D.PosSemidef := hAB.conjTranspose_mul_mul_same X⁻¹
    have h2 : Xᴴ * D * X = C := by
      calc Xᴴ * D * X = (X⁻¹ * X)ᴴ * C * (X⁻¹ * X) := by
            rw [hDdef, conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = C := by rw [hYX, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    have hEq : A = Xᴴ * (1 + D) * X := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h2, ← hBX, hCdef]
      abel
    have hdA : A.det = (1 + D).det * B.det := by
      rw [hEq, det_mul, det_mul, hBX, det_mul]; ring
    have hu := one_le_re_det_one_add D hD
    have hu0 : (1 + D).det.im = 0 :=
      ((Complex.nonneg_iff.mp (PosSemidef.one.add hD).det_nonneg).2).symm
    have hw := Complex.nonneg_iff.mp hB.det_nonneg
    rw [hdA, Complex.mul_re, hu0, zero_mul, sub_zero]
    nlinarith [hw.1]
end Bl.DetMonotoneStarMulSelf
end

set_option autoImplicit false
open Bl Bl.DetMonotoneStarMulSelf
namespace Bl.DetMonotoneStarMulSelf
theorem _root_.solution :
  ∀ (n : Nat), ReciprocityTheory.L2DbarEstimates.DetMonoStatement n := by
  intro n
  unfold ReciprocityTheory.L2DbarEstimates.DetMonoStatement
  intro A B hB hAB
  exact det_mono A B hB hAB
end Bl.DetMonotoneStarMulSelf
