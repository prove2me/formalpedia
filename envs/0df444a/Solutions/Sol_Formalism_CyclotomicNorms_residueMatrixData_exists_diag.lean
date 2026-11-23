-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.exists_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:39.590108+00:00
-- url     : https://prove2.me/submissions/0611769a-25de-4da3-a8b2-c60752679893

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_exists_dvd_all_of_total
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_det_blockExtend
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_mul_mul_eq_diagonal
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_isUnit_det_swap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_succ
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_succ

set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {R : Type*} [CommRing R]
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution (hR : ∀ x y : R, x ∣ y ∨ y ∣ x) : ∀ (a : ℕ) (M : Matrix (Fin a) (Fin a) R),
    ∃ P Q : Matrix (Fin a) (Fin a) R, IsUnit P.det ∧ IsUnit Q.det ∧
      ∃ d : Fin a → R, P * M * Q = diagonal d := by
  intro a
  induction a with
  | zero => intro M; exact ⟨1, 1, by simp, by simp, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ a ih =>
    intro M
    obtain ⟨⟨i0, j0⟩, -, hp⟩ := exists_dvd_all_of_total hR (Finset.univ : Finset (Fin (a+1) × Fin (a+1)))
      Finset.univ_nonempty (fun p => M p.1 p.2)
    set M1 := Matrix.swap R 0 i0 * M * Matrix.swap R 0 j0 with hM1
    have h00 : M1 0 0 = M i0 j0 := by simp [hM1]
    have hdvd : ∀ i j, M1 0 0 ∣ M1 i j := by
      intro i j
      rw [h00, hM1, Matrix.mul_apply]
      refine Finset.dvd_sum fun l _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.dvd_sum fun k _ => ?_
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hp (k, l) (Finset.mem_univ _)) _) _
    choose c hc using hdvd
    let Bl : Matrix (Fin (a+1)) (Fin (a+1)) R := Matrix.of fun i k => if i ≠ 0 ∧ k = 0 then c i 0 else 0
    let Br : Matrix (Fin (a+1)) (Fin (a+1)) R := Matrix.of fun k j => if k = 0 ∧ j ≠ 0 then c 0 j else 0
    have hL : (1 - Bl).det = 1 := by
      rw [Matrix.det_of_isLowerTriangular]
      · refine Finset.prod_eq_one fun i _ => ?_
        simp [Bl]
      · intro i j hij
        have hj : j ≠ 0 := by
          intro h; subst h; exact (Fin.not_lt_zero i) hij
        simp [Bl, hj, Matrix.one_apply]
        rintro rfl; exact absurd hij (lt_irrefl _)
    have hU : (1 - Br).det = 1 := by
      rw [Matrix.det_of_isUpperTriangular]
      · refine Finset.prod_eq_one fun i _ => ?_
        simp [Br]
      · intro i j hij
        have hi : i ≠ 0 := by
          intro h; subst h; exact (Fin.not_lt_zero j) hij
        simp [Br, hi, Matrix.one_apply]
        rintro rfl; exact absurd hij (lt_irrefl _)
    set E := (1 - Bl) * M1 * (1 - Br) with hE
    have hBl : ∀ i j, (Bl * M1) i j = if i ≠ 0 then c i 0 * M1 0 j else 0 := by
      intro i j
      simp only [Bl, Matrix.mul_apply, Matrix.of_apply]
      split_ifs with h <;> simp [h]
    have hBr : ∀ (X : Matrix (Fin (a+1)) (Fin (a+1)) R) i j,
        (X * Br) i j = if j ≠ 0 then X i 0 * c 0 j else 0 := by
      intro X i j
      simp only [Br, Matrix.mul_apply, Matrix.of_apply]
      split_ifs with h <;> simp [h]
    have hEij : ∀ i j, E i j = (M1 i j - if i ≠ 0 then c i 0 * M1 0 j else 0) -
        (if j ≠ 0 then (M1 i 0 - if i ≠ 0 then c i 0 * M1 0 0 else 0) * c 0 j else 0) := by
      intro i j
      rw [hE, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, hBr, Matrix.sub_mul, Matrix.one_mul,
        Matrix.sub_apply, Matrix.sub_apply, hBl, hBl]
    have hE00 : E 0 0 = M1 0 0 := by rw [hEij]; simp
    have hE1 : ∀ j : Fin a, E 0 j.succ = 0 := by
      intro j; rw [hEij]; simp [Fin.succ_ne_zero]; rw [hc 0 j.succ]; ring
    have hE2 : ∀ i : Fin a, E i.succ 0 = 0 := by
      intro i; rw [hEij]; simp [Fin.succ_ne_zero]; rw [hc i.succ 0]; ring
    obtain ⟨P', Q', hP', hQ', d', hd'⟩ := ih (Matrix.of fun i j : Fin a => E i.succ j.succ)
    refine ⟨ext1 P' * (1 - Bl) * Matrix.swap R 0 i0, Matrix.swap R 0 j0 * (1 - Br) * ext1 Q', ?_, ?_,
      Fin.cons (E 0 0) d', ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, det_blockExtend, hL, mul_one]
      exact hP'.mul (isUnit_det_swap _ _)
    · rw [Matrix.det_mul, Matrix.det_mul, det_blockExtend, hU, mul_one]
      exact (isUnit_det_swap _ _).mul hQ'
    · rw [← blockExtend_mul_mul_eq_diagonal P' Q' E hE1 hE2 d' hd', hE, hM1]
      simp only [Matrix.mul_assoc]
end Formalism.CyclotomicNorms.residueMatrixData
