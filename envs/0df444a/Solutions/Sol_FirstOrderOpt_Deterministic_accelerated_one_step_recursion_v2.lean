-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.accelerated_one_step_recursion_v2
-- status  : ACCEPTED   (disprove)
-- author  : @queelius
-- created : 2026-10-22T17:02:40.334894+00:00
-- url     : https://prove2.me/submissions/f533b6d1-e451-4719-903e-cd213656293b

import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

open FirstOrderOpt.Prox

set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def quadratic : ℝ → ℝ := fun x => x ^ 2 / 2

noncomputable def quadraticGrad (x : ℝ) : ℝ →L[ℝ] ℝ :=
  x • ContinuousLinearMap.id ℝ ℝ

theorem quadratic_deriv (x : ℝ) : HasFDerivAt quadratic (quadraticGrad x) x := by
  convert (((hasDerivAt_id x).pow 2).div_const 2).hasFDerivAt using 1 <;>
    norm_num [quadratic, quadraticGrad] <;> first
    | rfl
    | (apply ContinuousLinearMap.ext; intro z; simp [mul_comm])

noncomputable def quadraticDGF : DistanceGeneratingFunction (Set.univ : Set ℝ) where
  ω := quadratic
  dω := quadraticGrad
  hasFDerivWithinAt := fun x _ => (quadratic_deriv x).hasFDerivWithinAt
  continuousOn_dω := (continuous_id.smul continuous_const).continuousOn
  strongConvex := by
    intro x _ y _
    simp only [quadratic, quadraticGrad, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs]
    nlinarith

theorem quadratic_V (x y : ℝ) : quadraticDGF.V x y = (y - x) ^ 2 / 2 := by
  simp only [DistanceGeneratingFunction.V, quadraticDGF, quadratic, quadraticGrad,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

theorem quadratic_smooth (x y : ℝ) : ‖quadraticGrad x - quadraticGrad y‖ ≤ 1 * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖x * z - y * z‖ ≤ (1 * ‖x - y‖) * ‖z‖
  rw [← sub_mul, norm_mul, one_mul]

theorem quadratic_strong (x y : ℝ) :
    quadratic x + quadraticGrad x (y - x) + 1 * quadraticDGF.V x y ≤ quadratic y := by
  rw [quadratic_V]
  simp only [quadratic, quadraticGrad, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  nlinarith

theorem bad_prox_min (x : ℝ) :
    2 * quadraticGrad 1 0 + 1 * quadraticDGF.V 1 0 + quadraticDGF.V 1 0 ≤
      2 * quadraticGrad 1 x + 1 * quadraticDGF.V 1 x + quadraticDGF.V 1 x := by
  simp only [quadratic_V, quadraticGrad, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  nlinarith [sq_nonneg x]

/-- The original conclusion's left side minus its right side, for every comparator. -/
theorem missing_scale_residual (x : ℝ) :
    (quadratic (1 / 2) - quadratic x + (1 / 2) * (1 + 1 / 2) * quadraticDGF.V 0 x) -
      ((1 - 1 / 2) * (quadratic 1 - quadratic x) + ((1 / 2) / 2) * quadraticDGF.V 1 x) =
        (x - 1) / 4 := by
  simp only [quadratic_V, quadratic]
  ring

/-- Restoring the missing factor changes this example's prox minimizer to 1/3. -/
theorem restored_scale_prox_min (x : ℝ) :
    2 * quadraticGrad 1 (1 / 3) + (2 * 1) * quadraticDGF.V 1 (1 / 3) + quadraticDGF.V 1 (1 / 3) ≤
      2 * quadraticGrad 1 x + (2 * 1) * quadraticDGF.V 1 x + quadraticDGF.V 1 x := by
  simp only [quadratic_V, quadraticGrad, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  nlinarith [sq_nonneg (x - 1 / 3)]

/-- Control for this quadratic example, not a proof of the general repaired theorem. -/
theorem restored_scale_residual (x : ℝ) :
    (quadratic (2 / 3) - quadratic x + (1 / 2) * (1 + 1 / 2) * quadraticDGF.V (1 / 3) x) -
      ((1 - 1 / 2) * (quadratic 1 - quadratic x) + ((1 / 2) / 2) * quadraticDGF.V 1 x) =
        -(1 / 9) := by
  simp only [quadratic_V, quadratic]
  ring

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f : E → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ)
    (fGrad : E → E →L[ℝ] ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (hStrConv : ∀ x ∈ X, ∀ y ∈ X, f x + (fGrad x) (y - x) + μ * ν.V x y ≤ f y)
    (xPrev xBarPrev xTilde xNew xBarNew : E)
    (hxPrev : xPrev ∈ X) (hxBarPrev : xBarPrev ∈ X) (hxNew : xNew ∈ X)
    (q γ α : ℝ) (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hTilde : xTilde = (1 - q) • xBarPrev + q • xPrev)
    (hNewMin : ∀ x ∈ X, γ * (fGrad xTilde) xNew + μ * ν.V xTilde xNew + ν.V xPrev xNew ≤
      γ * (fGrad xTilde) x + μ * ν.V xTilde x + ν.V xPrev x)
    (hBarNew : xBarNew = (1 - α) • xBarPrev + α • xNew)
    (h7 : q ≤ α) (h8 : L * (α - q) / (1 - q) ≤ μ) (h9 : L * q * (1 - α) / (1 - q) ≤ 1 / γ),
    ∀ x ∈ X, f xBarNew - f x + α * (μ + 1 / γ) * ν.V xNew x ≤
      (1 - α) * (f xBarPrev - f x) + (α / γ) * ν.V xPrev x) := by
  intro h
  have hc := h (E := ℝ) Set.univ (convex_univ) isClosed_univ quadraticDGF
    quadratic 1 1 (by norm_num) (by norm_num) quadraticGrad
    (fun x _ => (quadratic_deriv x).hasFDerivWithinAt)
    (fun x _ y _ => quadratic_smooth x y)
    (fun x _ y _ => quadratic_strong x y)
    1 1 1 0 (1 / 2) (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
    (1 / 2) 2 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [smul_eq_mul])
    (fun x _ => bad_prox_min x) (by norm_num [smul_eq_mul])
    (by norm_num) (by norm_num) (by norm_num) 2 (Set.mem_univ _)
  norm_num [quadratic, quadratic_V] at hc
