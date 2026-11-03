-- Prove2me | solution 1 for ConleyZehnder.rhoHat_ne_one_of_trace_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T16:11:54.067483+00:00
-- url     : https://prove2.me/submissions/805e8e60-6cab-465b-875e-6cfc9ede769f

import Definitions.Def_ConleyZehnder_Setting
import Theorems.Thm_ConleyZehnder_complexLinearDet_ne_zero
import Definitions.Def_HryniewiczCriterion_GraphAngle

open ConleyZehnder HryniewiczCriterion Matrix

namespace CZBH

noncomputable section

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

theorem trace_mat1 (A : Mat 1) : A.trace = A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.trace, Fintype.sum_sum_type]


theorem det_mat1 (A : Mat 1) : A.det = A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) * A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) - A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) * A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) := by
  rw [← Matrix.det_reindex_self finSumFinEquiv A, Matrix.det_fin_two]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl


theorem cld_mat1 (A : Mat 1) :
    complexLinearDet A = ⟨(A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)) / 2, (A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) - A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)) / 2⟩ := by
  unfold complexLinearDet complexLinearPart
  rw [Matrix.det_unique]
  apply Complex.ext <;>
    simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, Matrix.fromBlocks] <;> ring


theorem det_eq_one (A : Mat 1) (hA : IsSymplectic A) : A.det = 1 := by
  have h := (SymplecticGroup.mem_iff (A := A)).1 hA
  have h' := congrFun (congrFun h (Sum.inl 0 : Fin 1 ⊕ Fin 1)) (Sum.inr 0 : Fin 1 ⊕ Fin 1)
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.transpose_apply] at h'
  rw [det_mat1]
  linarith


theorem det_one_sub (A : Mat 1) (hA : IsSymplectic A) : (1 - A).det = 2 - A.trace := by
  have h := det_eq_one A hA
  rw [det_mat1] at h
  rw [det_mat1, trace_mat1]
  simp [Matrix.sub_apply, Matrix.one_apply]
  linarith


theorem rhoHat_re_pos (A : Mat 1) (hA : IsSymplectic A) (htr : 0 < A.trace) :
    0 < (rhoHat A).re := by
  have hne := complexLinearDet_ne_zero A hA
  have hn : 0 < ‖complexLinearDet A‖ := norm_pos_iff.2 hne
  unfold rhoHat
  rw [Complex.div_ofReal_re]
  apply div_pos _ hn
  rw [cld_mat1, trace_mat1] at *
  simp only
  linarith


theorem rhoHat_ne_one (A : Mat 1) (hA : IsSymplectic A) (htr : A.trace < 2) :
    rhoHat A ≠ 1 := by
  intro h1
  have hne := complexLinearDet_ne_zero A hA
  have hn : (‖complexLinearDet A‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hne
  have he : complexLinearDet A = (‖complexLinearDet A‖ : ℂ) := by
    unfold rhoHat at h1
    rw [div_eq_one_iff_eq hn] at h1
    exact h1
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  have hpos : 0 < ‖complexLinearDet A‖ := norm_pos_iff.2 hne
  rw [cld_mat1] at hre him hpos
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hdet := det_eq_one A hA
  rw [det_mat1] at hdet
  rw [trace_mat1] at htr
  have hc : A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) = A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by linarith
  rw [hc] at hdet
  have hs : 0 < A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by linarith
  nlinarith [sq_nonneg (A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) - A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)), sq_nonneg (A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)), mul_pos hs (by linarith : (0:ℝ) < 2 - (A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)))]


def dotv (M : M2) (s : ℝ) : ℝ :=
  M 0 0 * Real.cos s ^ 2 + (M 0 1 + M 1 0) * Real.cos s * Real.sin s + M 1 1 * Real.sin s ^ 2


def crossv (M : M2) (s : ℝ) : ℝ :=
  M 1 0 * Real.cos s ^ 2 + (M 1 1 - M 0 0) * Real.cos s * Real.sin s - M 0 1 * Real.sin s ^ 2


theorem mulVec_rv (M : M2) (s : ℝ) :
    M *ᵥ rotationVector s = ![dotv M s * Real.cos s - crossv M s * Real.sin s,
      dotv M s * Real.sin s + crossv M s * Real.cos s] := by
  have h := Real.sin_sq_add_cos_sq s
  ext i; fin_cases i <;>
    simp [rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two, dotv, crossv]
  · linear_combination (-(M 0 0 * Real.cos s) - M 0 1 * Real.sin s) * h
  · linear_combination (-(M 1 0 * Real.cos s) - M 1 1 * Real.sin s) * h


theorem dotProduct_eq (M : M2) (s : ℝ) :
    rotationVector s ⬝ᵥ (M *ᵥ rotationVector s) = dotv M s := by
  have h := Real.sin_sq_add_cos_sq s
  rw [mulVec_rv]
  simp [rotationVector, dotProduct, Fin.sum_univ_two]
  linear_combination dotv M s * h


theorem rot_mul_apply0 (a : ℝ) (M : M2) (j : Fin 2) :
    (rotationMatrix a * M) 0 j = Real.cos a * M 0 j - Real.sin a * M 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [rotationMatrix]; ring


theorem rot_mul_apply1 (a : ℝ) (M : M2) (j : Fin 2) :
    (rotationMatrix a * M) 1 j = Real.sin a * M 0 j + Real.cos a * M 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [rotationMatrix]


theorem rv_ne_zero (s : ℝ) : rotationVector s ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotationVector] at h0 h1
  have := Real.sin_sq_add_cos_sq s
  rw [h0, h1] at this; norm_num at this


end

end CZBH

open ConleyZehnder

theorem solution (A : Mat 1) (hA : IsSymplectic A) (htr : A.trace < 2) :
    rhoHat A ≠ 1 :=
  CZBH.rhoHat_ne_one A hA htr
