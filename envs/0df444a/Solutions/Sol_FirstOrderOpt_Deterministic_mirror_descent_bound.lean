-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.mirror_descent_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:47:01.326134+00:00
-- url     : https://prove2.me/submissions/d47410cf-892b-4b65-85ce-86aa4b82463e

import Mathlib

namespace FirstOrderOpt.Deterministic

/-- The concrete counterexample on `E = ℝ`: `X = univ`, `V = 0`, `dV = 0`, `g = 0`,
`γ = 1`, iterates `0, 2, 2, …`, and the nonconvex objective `f y = (y (y - 2))²`. -/
theorem aux_mdb_counterexample :
    let f : ℝ → ℝ := fun y => (y * (y - 2)) ^ 2
    let x : ℕ → ℝ := fun t => if t = 0 then 0 else 2
    let γ : ℕ → ℝ := fun _ => 1
    ¬ (f ((∑ t ∈ Finset.Icc 0 1, γ t)⁻¹ • ∑ t ∈ Finset.Icc 0 1, γ t • x t) - f 0 ≤
      (∑ t ∈ Finset.Icc 0 1, γ t)⁻¹ *
        ((fun _ _ => (0 : ℝ)) (x 0) (0 : ℝ) +
          (1 / 2) * (1 : ℝ) ^ 2 * ∑ t ∈ Finset.Icc 0 1, (γ t) ^ 2)) := by
  intro f x γ
  have hI : Finset.Icc 0 1 = ({0, 1} : Finset ℕ) := by decide
  simp only [f, x, γ, hI]
  rw [Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)]
  norm_num

end FirstOrderOpt.Deterministic

open FirstOrderOpt.Deterministic

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (V : E → E → ℝ) (dV : E → E → E →L[ℝ] ℝ) (M : ℝ) (hM : 0 < M)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (γ : ℕ → ℝ)
    (hx : ∀ t, x t ∈ X) (hγ : ∀ t, 0 < γ t) (hgnorm : ∀ t, ‖g t‖ ≤ M)
    (hVnonneg : ∀ y ∈ X, ∀ z ∈ X, 0 ≤ V y z)
    (hVthreepoint : ∀ y ∈ X, ∀ z ∈ X, ∀ w ∈ X, V y w = V y z + (dV y z) (w - z) + V z w)
    (hsub : ∀ t, ∀ y ∈ X, f (x t) + (g t) (y - x t) ≤ f y)
    (hmin : ∀ t, ∀ y ∈ X, γ t * (g t) (x (t + 1)) + V (x t) (x (t + 1)) ≤
      γ t * (g t) y + V (x t) y)
    (s k : ℕ) (hsk : s ≤ k)
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, f xstar ≤ f y)
    (xbar : E)
    (hxbar : xbar = (∑ t ∈ Finset.Icc s k, γ t)⁻¹ • ∑ t ∈ Finset.Icc s k, γ t • x t),
    f xbar - f xstar ≤ (∑ t ∈ Finset.Icc s k, γ t)⁻¹ *
      (V (x s) xstar + (1 / 2) * M ^ 2 * ∑ t ∈ Finset.Icc s k, (γ t) ^ 2)) := by
  intro H
  refine aux_mdb_counterexample (H (E := ℝ) Set.univ
    (fun y => (y * (y - 2)) ^ 2) (fun _ _ => 0) (fun _ _ => 0) 1 one_pos
    (fun t => if t = 0 then 0 else 2) (fun _ => 0) (fun _ => 1)
    (fun _ => Set.mem_univ _) (fun _ => one_pos) (fun _ => by simp)
    (fun _ _ _ _ => le_refl _) (fun _ _ _ _ _ _ => by simp)
    ?_ (fun _ _ _ => by simp) 0 1 (by norm_num) 0 (Set.mem_univ _) ?_ _ rfl)
  · intro t y _
    simp only [zero_apply, add_zero]
    split_ifs <;> norm_num <;> positivity
  · intro y _
    norm_num
    positivity
