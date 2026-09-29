-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.accelerated_gradient_rate
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:01:26.200072+00:00
-- url     : https://prove2.me/submissions/7282f06d-fb55-4efa-bd65-4a509257f563

import Mathlib

namespace FirstOrderOpt.Deterministic

/-- The linear functional `y ↦ a * y` on `ℝ`, used as the gradient of `y ↦ y²/2`. -/
noncomputable def aux_agr_grad (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.id ℝ ℝ

theorem aux_agr_grad_apply (a b : ℝ) : aux_agr_grad a b = a * b := rfl

end FirstOrderOpt.Deterministic

open FirstOrderOpt.Deterministic

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (V : E → E → ℝ) (dV : E → E → E →L[ℝ] ℝ) (L : ℝ) (hL : 0 < L)
    (fGrad : E → E →L[ℝ] ℝ)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - (fGrad x) (y - x) ≤ (L / 2) * ‖y - x‖ ^ 2)
    (hVnonneg : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ V x z)
    (hVthreepoint : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, V x z = V x y + (dV x y) (z - y) + V y z)
    (x xTilde xBar : ℕ → E)
    (hx : ∀ t, x t ∈ X) (hxBar : ∀ t, xBar t ∈ X) (hxTilde : ∀ t, 1 ≤ t → xTilde t ∈ X)
    (k : ℕ) (hk : 1 ≤ k)
    (hTildeDef : ∀ t : ℕ, 1 ≤ t → t ≤ k →
      xTilde t = (1 - 2 / ((t : ℝ) + 1)) • xBar (t - 1) + (2 / ((t : ℝ) + 1)) • x (t - 1))
    (hxDef : ∀ t : ℕ, 1 ≤ t → t ≤ k → ∀ y ∈ X,
      ((t : ℝ) / (2 * L)) * (fGrad (xTilde t)) (x t) + V (x (t - 1)) (x t) ≤
        ((t : ℝ) / (2 * L)) * (fGrad (xTilde t)) y + V (x (t - 1)) y)
    (hBarDef : ∀ t : ℕ, 1 ≤ t → t ≤ k →
      xBar t = (1 - 2 / ((t : ℝ) + 1)) • xBar (t - 1) + (2 / ((t : ℝ) + 1)) • x t)
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, f xstar ≤ f y),
    f (xBar k) - f xstar ≤ (4 * L) / ((k : ℝ) * ((k : ℝ) + 1)) * V (x 0) xstar) := by
  intro H
  -- Counterexample: `E = ℝ`, `X = [-1,1]`, `f y = y²/2`, `V = 0`, `dV = 0`, `L = 1`,
  -- `k = 1`, `x 0 = xTilde 1 = 1`, `x 1 = xBar 1 = xBar 0 = -1`, `x* = 0`.
  let X : Set ℝ := Set.Icc (-1) 1
  let xs : ℕ → ℝ := fun t => if t = 0 then 1 else -1
  have hmem : ∀ t, xs t ∈ X := by
    intro t
    by_cases ht : t = 0
    · simp [xs, X, ht]
    · simp [xs, X, ht]
  have h1mem : (1 : ℝ) ∈ X := by simp [X]
  have hm1mem : (-1 : ℝ) ∈ X := by simp [X]
  have h0mem : (0 : ℝ) ∈ X := by simp [X]
  have key := H (E := ℝ) X (fun y => y ^ 2 / 2) (fun _ _ => 0) (fun _ _ => 0)
    1 one_pos aux_agr_grad ?smooth (fun _ _ _ _ => le_refl _) (fun _ _ _ _ _ _ => by simp)
    xs (fun _ => 1) (fun _ => -1)
    hmem (fun _ => hm1mem) (fun _ _ => h1mem) 1 le_rfl
    ?tilde ?xdef ?bar
    0 h0mem ?opt
  · norm_num at key
  case smooth =>
    intro a _ b _
    rw [aux_agr_grad_apply, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (b - a)]
  case tilde =>
    intro t ht1 htk
    have ht : t = 1 := le_antisymm htk ht1
    subst ht
    norm_num [xs]
  case xdef =>
    intro t ht1 htk y hy
    have ht : t = 1 := le_antisymm htk ht1
    subst ht
    simp only [aux_agr_grad_apply, xs, X, Set.mem_Icc] at hy ⊢
    norm_num
    linarith [hy.1]
  case bar =>
    intro t ht1 htk
    have ht : t = 1 := le_antisymm htk ht1
    subst ht
    norm_num [xs]
  case opt =>
    intro y _
    show ((0 : ℝ)) ^ 2 / 2 ≤ y ^ 2 / 2
    nlinarith [sq_nonneg y]
