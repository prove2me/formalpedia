-- Prove2me | solution 1 for FirstOrderOpt.FiniteSum.variance_reduced_progress_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:24:04.494238+00:00
-- url     : https://prove2.me/submissions/48475ff9-f4bf-4015-8c84-192c078b0442

import Mathlib

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x)
    (V : E → E → ℝ)
    (gradf_full : E → E →L[ℝ] ℝ)
    (L : ℝ) (hL : 0 < L) (hsmooth : ∀ x y, ‖gradf_full x - gradf_full y‖ ≤ L * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hstrong : ∀ x y, f y ≥ f x + (gradf_full x) (y - x) + μ * V x y)
    (γ : ℝ) (hγ : 0 < γ) (hLγ : L * γ ≤ 1 / 2)
    (xt xt1 : E) (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (Gt δt : E →L[ℝ] ℝ) (hδt : δt = Gt - gradf_full xt)
    (hmin : ∀ y ∈ X, γ * (Gt xt1) + γ * h xt1 + V xt xt1 ≤ γ * (Gt y) + γ * h y + V xt y),
    ∀ x ∈ X, γ * (Ψ xt1 - Ψ x) + V xt1 x ≤
      (1 - γ * μ) * V xt x + γ * (δt (x - xt)) + γ ^ 2 * ‖δt‖ ^ 2) := by
  intro H
  have := @H ℝ _ _ Set.univ (fun _ => 0) (fun _ => 0) (fun _ => 0) (by intro; simp)
    (fun a b => if a = 1 ∧ b = 0 then 1 else 0) (fun _ => 0) 1 one_pos
    (by intro x y; simp) 0 le_rfl (by intro x y; simp) (1/2) (by norm_num) (by norm_num)
    0 1 trivial trivial 0 0 (by simp) (by intro y _; simp) 0 trivial
  norm_num at this
