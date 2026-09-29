-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.accelerated_one_step_recursion
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:49:44.190472+00:00
-- url     : https://prove2.me/submissions/c2e376fd-c971-4d4e-89bc-661011503b4b

import Mathlib

namespace FirstOrderOpt.Deterministic

/-- The linear functional `y ↦ a * y` on `ℝ`, used as the gradient of `y ↦ y²/2`. -/
noncomputable def aux_aosr_grad (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.id ℝ ℝ

theorem aux_aosr_grad_apply (a b : ℝ) : aux_aosr_grad a b = a * b := rfl

end FirstOrderOpt.Deterministic

open FirstOrderOpt.Deterministic

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (V : E → E → ℝ) (dV : E → E → E →L[ℝ] ℝ) (L μ : ℝ) (hL : 0 < L)
    (hμ : 0 ≤ μ)
    (fGrad : E → E →L[ℝ] ℝ)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - (fGrad x) (y - x) ≤ (L / 2) * ‖y - x‖ ^ 2)
    (hStrConv : ∀ x ∈ X, ∀ y ∈ X, f x + (fGrad x) (y - x) + μ * V x y ≤ f y)
    (hVnonneg : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ V x z)
    (hVthreepoint : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, V x z = V x y + (dV x y) (z - y) + V y z)
    (xPrev xBarPrev xTilde xNew xBarNew : E)
    (hxPrev : xPrev ∈ X) (hxBarPrev : xBarPrev ∈ X) (hxTilde : xTilde ∈ X) (hxNew : xNew ∈ X)
    (hxBarNew : xBarNew ∈ X)
    (q γ α : ℝ) (hγ : 0 < γ)
    (hTilde : xTilde = (1 - q) • xBarPrev + q • xPrev)
    (hNewMin : ∀ x ∈ X, γ * (fGrad xTilde) xNew + μ * V xTilde xNew + V xPrev xNew ≤
      γ * (fGrad xTilde) x + μ * V xTilde x + V xPrev x)
    (hBarNew : xBarNew = (1 - α) • xBarPrev + α • xNew)
    (h7 : q ≤ α) (h8 : L * (α - q) / (1 - q) ≤ μ) (h9 : L * q * (1 - α) / (1 - q) ≤ 1 / γ),
    ∀ x ∈ X, f xBarNew - f x + α * (μ + 1 / γ) * V xNew x ≤
      (1 - α) * (f xBarPrev - f x) + (α / γ) * V xPrev x) := by
  intro H
  -- Counterexample: `E = ℝ`, `X = [-1,1]`, `f y = y²/2`, `V = 0`, `dV = 0`, `L = μ = 1`,
  -- `q = 0`, `γ = α = 1`, `xPrev = xBarPrev = xTilde = 1`, `xNew = xBarNew = -1`, `x = 0`.
  let X : Set ℝ := Set.Icc (-1) 1
  have h1mem : (1 : ℝ) ∈ X := by norm_num [X]
  have hm1mem : (-1 : ℝ) ∈ X := by norm_num [X]
  have h0mem : (0 : ℝ) ∈ X := by norm_num [X]
  have key := H (E := ℝ) X (fun y => y ^ 2 / 2) (fun _ _ => 0) (fun _ _ => 0)
    1 1 one_pos zero_le_one aux_aosr_grad ?smooth ?strconv (fun _ _ _ _ => le_refl _)
    (fun _ _ _ _ _ _ => by simp)
    1 1 1 (-1) (-1)
    h1mem h1mem h1mem hm1mem hm1mem 0 1 1 one_pos ?tilde ?newmin ?bar zero_le_one
    (by norm_num) (by norm_num) 0 h0mem
  · norm_num at key
  case smooth =>
    intro a _ b _
    rw [aux_aosr_grad_apply, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (b - a)]
  case strconv =>
    intro a _ b _
    rw [aux_aosr_grad_apply]
    nlinarith [sq_nonneg (b - a)]
  case tilde =>
    norm_num
  case newmin =>
    intro y hy
    rw [aux_aosr_grad_apply, aux_aosr_grad_apply]
    have := hy.1
    linarith
  case bar =>
    norm_num
