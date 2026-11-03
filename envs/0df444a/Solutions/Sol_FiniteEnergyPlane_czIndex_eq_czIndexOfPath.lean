-- Prove2me | solution 1 for FiniteEnergyPlane.czIndex_eq_czIndexOfPath
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T16:03:43.572188+00:00
-- url     : https://prove2.me/submissions/4b22dccc-5490-4e30-ac67-fe15b8278b6e

import Definitions.Def_FiniteEnergyPlane_Winding
import Definitions.Def_ConleyZehnder_Setting
import Theorems.Thm_ConleyZehnder_complexLinearDet_ne_zero
import Definitions.Def_HryniewiczCriterion_GraphAngle
import Theorems.Thm_ConleyZehnder_czIndex_one_eq_of_rhoHat_lift
import Theorems.Thm_HryniewiczCriterion_czIndexOfPath_eq_of_polarAngleLift
import Theorems.Thm_HryniewiczCriterion_exists_polarAngleLift

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

theorem czb_main (ψ : C(unitInterval, ConleyZehnder.Mat 1)) (hψ : ψ ∈ ConleyZehnder.SP 1) :
    ConleyZehnder.czIndex ψ = HryniewiczCriterion.czIndexOfPath (fun τ =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (ψ (Set.projIcc 0 1 zero_le_one τ))) := by
  set φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun τ =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv (ψ (Set.projIcc 0 1 zero_le_one τ)) with hφdef
  have hpi := Real.pi_pos
  have hproj : ∀ t : unitInterval, Set.projIcc 0 1 zero_le_one (t : ℝ) = t :=
    fun t => Set.projIcc_val zero_le_one t
  have hφt : ∀ t : unitInterval, φ t = Matrix.reindex finSumFinEquiv finSumFinEquiv (ψ t) :=
    fun t => by simp only [hφdef, hproj]
  have hent : ∀ (A : ConleyZehnder.Mat 1),
      (Matrix.reindex finSumFinEquiv finSumFinEquiv A) 0 0 = A (Sum.inl 0) (Sum.inl 0) ∧
      (Matrix.reindex finSumFinEquiv finSumFinEquiv A) 0 1 = A (Sum.inl 0) (Sum.inr 0) ∧
      (Matrix.reindex finSumFinEquiv finSumFinEquiv A) 1 0 = A (Sum.inr 0) (Sum.inl 0) ∧
      (Matrix.reindex finSumFinEquiv finSumFinEquiv A) 1 1 = A (Sum.inr 0) (Sum.inr 0) := by
    intro A
    refine ⟨rfl, rfl, rfl, rfl⟩
  have hc : ContinuousOn (fun t i j => φ t i j) (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun t : ℝ =>
      ψ (Set.projIcc 0 1 zero_le_one t) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
    exact (continuous_apply _).comp ((continuous_apply _).comp
      (ψ.continuous.comp continuous_projIcc))
  have h0 : φ 0 = 1 := by
    have := hφt 0
    simp only [Set.Icc.coe_zero] at this
    rw [this, hψ.2.1]
    simp
  have hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1 := by
    intro t ht
    have := hφt ⟨t, ht⟩
    simp only at this
    rw [this, Matrix.det_reindex_self]
    exact CZBH.det_eq_one _ (hψ.1 _)
  obtain ⟨α, hα⟩ := exists_polarAngleLift φ hc hdet h0
  -- `ρ̂ ∘ ψ = e^{iα}`
  have hρ : ∀ t : unitInterval, rhoHat (ψ t) = Complex.exp (α t * Complex.I) := by
    intro t
    obtain ⟨P, hP, hφP⟩ := hα.2.2 t t.2
    have hsym : P 1 0 = P 0 1 := by
      have := congrFun (congrFun hP.1 0) 1
      simpa [Matrix.conjTranspose_apply] using this
    have hp : 0 < P 0 0 := by
      have := hP.dotProduct_mulVec_pos (CZBH.rv_ne_zero 0)
      rw [star_trivial, CZBH.dotProduct_eq] at this; simpa [CZBH.dotv] using this
    have hu : 0 < P 1 1 := by
      have := hP.dotProduct_mulVec_pos (CZBH.rv_ne_zero (Real.pi / 2))
      rw [star_trivial, CZBH.dotProduct_eq] at this; simpa [CZBH.dotv] using this
    have e := hφt t
    rw [hφP] at e
    obtain ⟨e00, e01, e10, e11⟩ := hent (ψ t)
    have a00 := congrFun (congrFun e 0) 0
    have a01 := congrFun (congrFun e 0) 1
    have a10 := congrFun (congrFun e 1) 0
    have a11 := congrFun (congrFun e 1) 1
    rw [CZBH.rot_mul_apply0] at a00 a01
    rw [CZBH.rot_mul_apply1] at a10 a11
    rw [e00] at a00; rw [e01] at a01; rw [e10] at a10; rw [e11] at a11
    set r : ℝ := (P 0 0 + P 1 1) / 2 with hr
    have hrpos : 0 < r := by rw [hr]; linarith
    have hcld : complexLinearDet (ψ t) = (r : ℂ) * Complex.exp (α t * Complex.I) := by
      rw [CZBH.cld_mat1, ← a00, ← a01, ← a10, ← a11, hsym]
      apply Complex.ext
      · simp [Complex.exp_ofReal_mul_I_re, hr]; ring
      · simp [Complex.exp_ofReal_mul_I_im, hr]; ring
    unfold rhoHat
    rw [hcld, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpos]
    have : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    field_simp
  have hθ : IsArgLift (fun t => rhoHat (ψ t)) (fun t => α t) :=
    ⟨hα.1.comp_continuous continuous_subtype_val (fun t => t.2), hρ⟩
  have hα0 : α ((0 : unitInterval) : ℝ) = 0 := by simpa using hα.2.1
  have hα1 : α ((1 : unitInterval) : ℝ) = α 1 := by simp
  have htr : (ψ 1).trace = (φ 1).trace := by
    have := hφt 1
    simp only [Set.Icc.coe_one] at this
    rw [this, CZBH.trace_mat1, Matrix.trace_fin_two]
    obtain ⟨e00, -, -, e11⟩ := hent (ψ 1)
    rw [e00, e11]
  have hne2 : (ψ 1).trace ≠ 2 := by
    intro h
    apply hψ.2.2
    rw [CZBH.det_one_sub _ (hψ.1 1), h]; ring
  have hC1 := ConleyZehnder.czIndex_one_eq_of_rhoHat_lift ψ hψ (fun t => α t) hθ
  have hC2 := HryniewiczCriterion.czIndexOfPath_eq_of_polarAngleLift φ hc h0 (hdet 1 ⟨zero_le_one, le_rfl⟩) α hα
  simp only [hα0, hα1, sub_zero] at hC1
  rcases lt_or_gt_of_ne hne2 with hlt | hgt
  · -- trace < 2
    set k : ℤ := ⌊α 1 / (2 * Real.pi)⌋ with hk
    have hk1 : (k : ℝ) ≤ α 1 / (2 * Real.pi) := Int.floor_le _
    have hk2 : α 1 / (2 * Real.pi) < k + 1 := Int.lt_floor_add_one _
    have hk1' : 2 * Real.pi * k ≤ α 1 := by
      rw [le_div_iff₀ (by linarith)] at hk1; linarith
    have hk2' : α 1 < 2 * Real.pi * k + 2 * Real.pi := by
      rw [div_lt_iff₀ (by linarith)] at hk2; linarith
    have hk1'' : 2 * Real.pi * k < α 1 := by
      refine lt_of_le_of_ne hk1' fun e => ?_
      apply CZBH.rhoHat_ne_one (ψ 1) (hψ.1 1) hlt
      rw [hρ 1, hα1, ← e, Complex.exp_eq_one_iff]
      exact ⟨k, by push_cast; ring⟩
    rw [(hC1 k).2 hlt hk1'' hk2', (hC2 k).2 (htr ▸ hlt) hk1'' hk2']
  · -- trace > 2
    set k : ℤ := round (α 1 / (2 * Real.pi)) with hk
    have hround := abs_sub_round (α 1 / (2 * Real.pi))
    rw [← hk] at hround
    have hle : |α 1 - 2 * Real.pi * k| ≤ Real.pi := by
      have e : α 1 - 2 * Real.pi * k = 2 * Real.pi * (α 1 / (2 * Real.pi) - k) := by
        field_simp
      rw [e, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.pi)]
      nlinarith
    have hcos : 0 < Real.cos (α 1) := by
      have := CZBH.rhoHat_re_pos (ψ 1) (hψ.1 1) (by linarith)
      rw [hρ 1, hα1, Complex.exp_ofReal_mul_I_re] at this
      exact this
    have hcosk : Real.cos (α 1 - 2 * Real.pi * k) = Real.cos (α 1) := by
      rw [show α 1 - 2 * Real.pi * k = α 1 + (-k : ℤ) * (2 * Real.pi) by push_cast; ring,
        Real.cos_add_int_mul_two_pi]
    have hlt2 : |α 1 - 2 * Real.pi * k| < Real.pi / 2 := by
      by_contra hcon
      push_neg at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith)
      rw [Real.cos_abs, hcosk] at this
      linarith
    rw [(hC1 k).1 hgt hlt2, (hC2 k).1 (htr ▸ hgt) hlt2]

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (ψ : C(unitInterval, ConleyZehnder.Mat 1))
    (hψ : ψ ∈ ConleyZehnder.SP 1) :
    ConleyZehnder.czIndex ψ = HryniewiczCriterion.czIndexOfPath (fun τ =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (ψ (Set.projIcc 0 1 zero_le_one τ))) :=
  czb_main ψ hψ
