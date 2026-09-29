-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.accelerated_gradient_recursion_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:48:07.067047+00:00
-- url     : https://prove2.me/submissions/c0a1e549-3840-4087-b9d4-fde6ff2d730c

import Mathlib

namespace FirstOrderOpt.Deterministic

/-- The linear functional `y ↦ a * y` on `ℝ`, used as the gradient of `y ↦ y²/2`. -/
noncomputable def aux_agrb_grad (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.id ℝ ℝ

theorem aux_agrb_grad_apply (a b : ℝ) : aux_agrb_grad a b = a * b := rfl

end FirstOrderOpt.Deterministic

open FirstOrderOpt.Deterministic

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (V : E → E → ℝ) (dV : E → E → E →L[ℝ] ℝ) (L : ℝ) (hL : 0 < L)
    (fGrad : E → E →L[ℝ] ℝ)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - (fGrad x) (y - x) ≤ (L / 2) * ‖y - x‖ ^ 2)
    (hVnonneg : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ V x z)
    (hVthreepoint : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, V x z = V x y + (dV x y) (z - y) + V y z)
    (x xTilde xBar : ℕ → E) (q γ α : ℕ → ℝ)
    (hx : ∀ t, x t ∈ X) (hxBar : ∀ t, xBar t ∈ X) (hxTilde : ∀ t, 1 ≤ t → xTilde t ∈ X)
    (k : ℕ) (hk : 1 ≤ k)
    (hγpos : ∀ t, 1 ≤ t → t ≤ k → 0 < γ t) (hαpos : ∀ t, 1 ≤ t → t ≤ k → 0 < α t)
    (hTildeDef : ∀ t, 1 ≤ t → t ≤ k → xTilde t = (1 - q t) • xBar (t - 1) + (q t) • x (t - 1))
    (hxDef : ∀ t, 1 ≤ t → t ≤ k → ∀ y ∈ X,
      γ t * (fGrad (xTilde t)) (x t) + V (x (t - 1)) (x t) ≤
        γ t * (fGrad (xTilde t)) y + V (x (t - 1)) y)
    (hBarDef : ∀ t, 1 ≤ t → t ≤ k → xBar t = (1 - α t) • xBar (t - 1) + (α t) • x t)
    (h13 : ∀ t, 1 ≤ t → t ≤ k → α t = q t)
    (h14 : ∀ t, 1 ≤ t → t ≤ k → L * α t ≤ 1 / γ t)
    (h15 : ∀ t, 2 ≤ t → t ≤ k → γ t * (1 - α t) / α t ≤ γ (t - 1) / α (t - 1))
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, f xstar ≤ f y),
    f (xBar k) - f xstar + (α k / γ k) * V (x k) xstar ≤
      (α k * γ 1 * (1 - α 1) / (γ k * α 1)) * (f (xBar 0) - f xstar) +
        (α k / γ k) * V (x 0) xstar) := by
  intro H
  -- Counterexample: `E = ℝ`, `X = [-1,1]`, `f y = y²/2`, `V = 0`, `dV = 0`, `L = 1`,
  -- `k = 1`, `q = γ = α = 1`, `x 0 = xBar 0 = xTilde 1 = 1`, `x 1 = xBar 1 = -1`, `x* = 0`.
  let X : Set ℝ := Set.Icc (-1) 1
  let xs : ℕ → ℝ := fun t => if t = 0 then 1 else -1
  have hmem : ∀ t, xs t ∈ X := by
    intro t
    by_cases ht : t = 0
    · simp [xs, X, ht]
    · simp [xs, X, ht]
  have h1mem : (1 : ℝ) ∈ X := by simp [X]
  have h0mem : (0 : ℝ) ∈ X := by simp [X]
  have key := H (E := ℝ) X (fun y => y ^ 2 / 2) (fun _ _ => 0) (fun _ _ => 0)
    1 one_pos aux_agrb_grad ?smooth (fun _ _ _ _ => le_refl _) (fun _ _ _ _ _ _ => by simp)
    xs (fun _ => 1) xs (fun _ => 1) (fun _ => 1) (fun _ => 1)
    hmem hmem (fun _ _ => h1mem) 1 le_rfl (fun _ _ _ => one_pos) (fun _ _ _ => one_pos)
    ?tilde ?xdef ?bar (fun _ _ _ => rfl) (fun _ _ _ => by norm_num) ?h15
    0 h0mem ?opt
  · norm_num [xs] at key
  case smooth =>
    intro a _ b _
    rw [aux_agrb_grad_apply, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (b - a)]
  case tilde =>
    intro t ht1 htk
    have ht : t = 1 := le_antisymm htk ht1
    subst ht
    simp [xs]
  case xdef =>
    intro t ht1 htk y hy
    have ht : t = 1 := le_antisymm htk ht1
    subst ht
    simp only [aux_agrb_grad_apply, xs, X, Set.mem_Icc] at hy ⊢
    norm_num
    linarith [hy.1]
  case bar =>
    intro t ht1 htk
    have ht : t = 1 := le_antisymm htk ht1
    subst ht
    simp [xs]
  case h15 =>
    intro t ht2 htk
    omega
  case opt =>
    intro y _
    show ((0 : ℝ)) ^ 2 / 2 ≤ y ^ 2 / 2
    nlinarith [sq_nonneg y]
