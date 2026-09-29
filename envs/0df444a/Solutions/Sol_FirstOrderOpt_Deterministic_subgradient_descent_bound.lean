-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.subgradient_descent_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:56:25.819384+00:00
-- url     : https://prove2.me/submissions/c63b7903-54ac-4656-83de-076ad725808a

import Mathlib

namespace FirstOrderOpt.Deterministic

open scoped RealInnerProductSpace

/-- Counterexample in `E = ℝ` with the nonconvex feasible set `X = {0, 1}`, `f x = x`, `M = 1`,
`x t = 1`, `g t = 1`, `γ t = 1/2`, `s = 0`, `k = 1`, `x' = 0`. -/
theorem aux_sdb_counterexample :
    ¬ (∀ (X : Set ℝ) (f : ℝ → ℝ) (M : ℝ) (_hM : 0 < M)
    (_hLip : ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ M * ‖x - y‖)
    (x g : ℕ → ℝ) (γ : ℕ → ℝ)
    (_hx : ∀ t, x t ∈ X) (_hγ : ∀ t, 0 < γ t)
    (_hsub : ∀ t, ∀ y ∈ X, f (x t) + ⟪g t, y - x t⟫ ≤ f y)
    (_hmin : ∀ t, ∀ y ∈ X, γ t * ⟪g t, x (t + 1)⟫ + (1 / 2) * ‖x (t + 1) - x t‖ ^ 2 ≤
      γ t * ⟪g t, y⟫ + (1 / 2) * ‖y - x t‖ ^ 2)
    (s k : ℕ) (_hsk : s ≤ k),
    ∀ x' ∈ X, ∑ t ∈ Finset.Icc s k, γ t * (f (x t) - f x') ≤
      (1 / 2) * (‖x' - x s‖ ^ 2 + M ^ 2 * ∑ t ∈ Finset.Icc s k, (γ t) ^ 2)) := by
  intro H
  have hLip : ∀ x ∈ ({0, 1} : Set ℝ), ∀ y ∈ ({0, 1} : Set ℝ),
      |(fun z : ℝ => z) x - (fun z : ℝ => z) y| ≤ 1 * ‖x - y‖ := by
    intro x _ y _
    rw [one_mul, Real.norm_eq_abs]
  have hx : ∀ t : ℕ, (fun _ : ℕ => (1 : ℝ)) t ∈ ({0, 1} : Set ℝ) := by
    intro t; simp
  have hγ : ∀ t : ℕ, 0 < (fun _ : ℕ => (1 / 2 : ℝ)) t := by
    intro t; norm_num
  have hsub : ∀ t : ℕ, ∀ y ∈ ({0, 1} : Set ℝ),
      (fun z : ℝ => z) ((fun _ : ℕ => (1 : ℝ)) t) +
        ⟪(fun _ : ℕ => (1 : ℝ)) t, y - (fun _ : ℕ => (1 : ℝ)) t⟫ ≤ (fun z : ℝ => z) y := by
    intro t y _
    simp only [Real.inner_apply]
    linarith
  have hmin : ∀ t : ℕ, ∀ y ∈ ({0, 1} : Set ℝ),
      (fun _ : ℕ => (1 / 2 : ℝ)) t * ⟪(fun _ : ℕ => (1 : ℝ)) t, (fun _ : ℕ => (1 : ℝ)) (t + 1)⟫ +
        (1 / 2) * ‖(fun _ : ℕ => (1 : ℝ)) (t + 1) - (fun _ : ℕ => (1 : ℝ)) t‖ ^ 2 ≤
      (fun _ : ℕ => (1 / 2 : ℝ)) t * ⟪(fun _ : ℕ => (1 : ℝ)) t, y⟫ +
        (1 / 2) * ‖y - (fun _ : ℕ => (1 : ℝ)) t‖ ^ 2 := by
    intro t y hy
    rcases hy with rfl | hy
    · simp only [Real.inner_apply, Real.norm_eq_abs]; norm_num
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      simp only [Real.inner_apply, Real.norm_eq_abs]; norm_num
  have h := H ({0, 1} : Set ℝ) (fun z => z) 1 one_pos hLip (fun _ => 1) (fun _ => 1)
    (fun _ => 1 / 2) hx hγ hsub hmin 0 1 (by norm_num) 0 (by simp)
  simp only [Finset.sum_const, Nat.card_Icc, Real.norm_eq_abs] at h
  norm_num at h

end FirstOrderOpt.Deterministic

open FirstOrderOpt.Deterministic
open scoped RealInnerProductSpace

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f : E → ℝ) (M : ℝ) (hM : 0 < M)
    (hLip : ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ M * ‖x - y‖)
    (x g : ℕ → E) (γ : ℕ → ℝ)
    (hx : ∀ t, x t ∈ X) (hγ : ∀ t, 0 < γ t)
    (hsub : ∀ t, ∀ y ∈ X, f (x t) + ⟪g t, y - x t⟫ ≤ f y)
    (hmin : ∀ t, ∀ y ∈ X, γ t * ⟪g t, x (t + 1)⟫ + (1 / 2) * ‖x (t + 1) - x t‖ ^ 2 ≤
      γ t * ⟪g t, y⟫ + (1 / 2) * ‖y - x t‖ ^ 2)
    (s k : ℕ) (hsk : s ≤ k),
    ∀ x' ∈ X, ∑ t ∈ Finset.Icc s k, γ t * (f (x t) - f x') ≤
      (1 / 2) * (‖x' - x s‖ ^ 2 + M ^ 2 * ∑ t ∈ Finset.Icc s k, (γ t) ^ 2)) := by
  intro H
  exact aux_sdb_counterexample
    (fun X f M hM hLip x g γ hx hγ hsub hmin s k hsk => H X f M hM hLip x g γ hx hγ hsub hmin s k hsk)
