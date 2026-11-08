-- Prove2me | solution 1 for BBPSSW.Distill.bilateral_rotation_bell
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:27:22.501197+00:00
-- url     : https://prove2.me/submissions/7884ba4a-4113-4eec-ac1e-26408fe8c51e

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_BBPSSW_Distill_bellVec
import Definitions.Def_BBPSSW_Distill_halfPiRot
import Definitions.Def_BBPSSW_Distill_bilateral
import Definitions.Def_BBPSSW_Distill_bilMap

namespace Aux_BBPSSW_rot

theorem hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem hhalf : ((Real.sqrt 2 : ℝ) : ℂ) / 2 = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [div_mul_eq_mul_div, hs]; norm_num

theorem hu3 : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 3 = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ / 2 := by
  rw [pow_succ, sq, ← mul_inv, hs]; ring

theorem hu2 : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 2 := by
  rw [sq, ← mul_inv, hs]; norm_num

end Aux_BBPSSW_rot

open BBPSSW.Distill in
theorem solution (a : Axis) (b : BellLabel) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      QAlgorithms.act (bilateral (halfPiRot a)) (bellVec b) = c • bellVec (bilMap a b) := by
  cases a <;> cases b
  · exact ⟨1, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨-Complex.I, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨-Complex.I, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨1, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨1, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨-1, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨1, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨1, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨1, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨1, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨-Complex.I, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
  · exact ⟨-Complex.I, by simp, by
    (
    unfold QAlgorithms.act BBPSSW.Distill.bilateral
    ext x
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
    simp [BBPSSW.Distill.halfPiRot, BBPSSW.Distill.pauli, BBPSSW.Distill.bellVec,
      BBPSSW.Distill.bilMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kronecker_apply] <;>
    (try simp only [Aux_BBPSSW_rot.hhalf]) <;>
    (have h3 := Aux_BBPSSW_rot.hu3) <;>
    (have h2 := Aux_BBPSSW_rot.hu2) <;>
    (generalize (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = u at h2 h3 ⊢) <;>
    (try ring_nf) <;>
    (try simp only [h3, Complex.I_sq]) <;>
    (try ring_nf) <;>
    (try simp only [h2, h3]) <;>
    ring_nf)⟩
