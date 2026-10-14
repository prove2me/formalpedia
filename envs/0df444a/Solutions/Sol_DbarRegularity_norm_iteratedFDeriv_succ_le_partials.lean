-- Prove2me | solution 1 for DbarRegularity.norm_iteratedFDeriv_succ_le_partials
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T15:10:34.6169+00:00
-- url     : https://prove2.me/submissions/6cdb6519-2c2d-45bd-bf1e-e9f1cb3576bc

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Basic



namespace DbarRegularity

open scoped ContDiff

/-- The `(j+1)`-st derivative of a map on `ℂ` is bounded pointwise by the `j`-th derivatives of
its two partial derivatives `∂φ/∂s = Dφ(·) 1` and `∂φ/∂t = Dφ(·) i`. -/
theorem norm_iteratedFDeriv_succ_le_partials {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {φ : ℂ → F} (j : ℕ) (hφ : ContDiff ℝ (j + 1) φ) (z : ℂ) :
    ‖iteratedFDeriv ℝ (j + 1) φ z‖
      ≤ ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ φ x 1) z‖
        + ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ φ x Complex.I) z‖ := by
  have hfd : ContDiff ℝ j (fderiv ℝ φ) := hφ.fderiv_right le_rfl
  let L₁ : F →L[ℝ] (ℂ →L[ℝ] F) := LinearMap.mkContinuous
    { toFun := fun y => Complex.reCLM.smulRight y
      map_add' := fun a b => ContinuousLinearMap.ext fun v => by simp [smul_add]
      map_smul' := fun c a => ContinuousLinearMap.ext fun v => by simp [smul_smul, mul_comm] }
    1 (fun y => by simp [ContinuousLinearMap.norm_smulRight_apply, Complex.reCLM_norm])
  let L₂ : F →L[ℝ] (ℂ →L[ℝ] F) := LinearMap.mkContinuous
    { toFun := fun y => Complex.imCLM.smulRight y
      map_add' := fun a b => ContinuousLinearMap.ext fun v => by simp [smul_add]
      map_smul' := fun c a => ContinuousLinearMap.ext fun v => by simp [smul_smul, mul_comm] }
    1 (fun y => by simp [ContinuousLinearMap.norm_smulRight_apply, Complex.imCLM_norm])
  have hL₁ : ‖L₁‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hL₂ : ‖L₂‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have h1 : ContDiff ℝ j (fun x => fderiv ℝ φ x 1) := hfd.clm_apply contDiff_const
  have h2 : ContDiff ℝ j (fun x => fderiv ℝ φ x Complex.I) := hfd.clm_apply contDiff_const
  have hdecomp : fderiv ℝ φ
      = fun x => L₁ (fderiv ℝ φ x 1) + L₂ (fderiv ℝ φ x Complex.I) := by
    funext x
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      apply Complex.ext <;> simp
    simp only [L₁, L₂, ContinuousLinearMap.add_apply, LinearMap.mkContinuous_apply,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply]
    calc fderiv ℝ φ x v = fderiv ℝ φ x (v.re • (1 : ℂ) + v.im • Complex.I) :=
          congrArg _ hv
      _ = _ := by rw [map_add, map_smul, map_smul]
  rw [← norm_iteratedFDeriv_fderiv (x := z)]
  conv_lhs => rw [hdecomp]
  have hA : ContDiff ℝ j (fun x => L₁ (fderiv ℝ φ x 1)) := L₁.contDiff.comp h1
  have hB : ContDiff ℝ j (fun x => L₂ (fderiv ℝ φ x Complex.I)) := L₂.contDiff.comp h2
  rw [iteratedFDeriv_add_apply' hA.contDiffAt hB.contDiffAt]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have h := L₁.norm_iteratedFDeriv_comp_left (x := z) (n := j) h1.contDiffAt le_rfl
    refine le_trans h ?_
    have := mul_le_mul_of_nonneg_right hL₁
      (norm_nonneg (iteratedFDeriv ℝ j (fun x => fderiv ℝ φ x 1) z))
    exact this.trans_eq (one_mul _)
  · have h := L₂.norm_iteratedFDeriv_comp_left (x := z) (n := j) h2.contDiffAt le_rfl
    refine le_trans h ?_
    have := mul_le_mul_of_nonneg_right hL₂
      (norm_nonneg (iteratedFDeriv ℝ j (fun x => fderiv ℝ φ x Complex.I) z))
    exact this.trans_eq (one_mul _)

end DbarRegularity

open DbarRegularity

open scoped ContDiff

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {φ : ℂ → F} (j : ℕ) (hφ : ContDiff ℝ (j + 1) φ) (z : ℂ) :
    ‖iteratedFDeriv ℝ (j + 1) φ z‖
      ≤ ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ φ x 1) z‖
        + ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ φ x Complex.I) z‖ :=
  norm_iteratedFDeriv_succ_le_partials j hφ z
