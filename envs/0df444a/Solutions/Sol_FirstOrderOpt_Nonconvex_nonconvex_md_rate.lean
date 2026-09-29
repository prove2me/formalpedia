-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.nonconvex_md_rate
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:21:12.670831+00:00
-- url     : https://prove2.me/submissions/c34bd0da-d821-4d4d-8169-d76ff4e957cb

import Mathlib

open scoped RealInnerProductSpace

/-- Counterexample: nothing constrains `V` (the book's Bregman distance). With `V = 0`,
`f = h = 0` and `fGrad = 0` every point is a generalized projection, so the iterates
`x k = k` in `E = ℝ` are admissible. With `L = 1`, `N = 1` and `R = 1` we get `Ψ* = 0`,
`DΨ = 0` and `‖gX 1‖² = 1`, while the claimed bound is `2 L² DΨ² / N = 0`. -/
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h : E → ℝ) (V : E → E → ℝ) (L : ℝ) (hL : 0 < L) (fGrad : E → E)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - ⟪fGrad x, y - x⟫ ≤ (L / 2) * ‖y - x‖ ^ 2)
    (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → E) (gX : ℕ → E)
    (hx : ∀ k, x k ∈ X)
    (hxDef : ∀ k, 1 ≤ k → k ≤ N → ∀ u ∈ X,
      ⟪fGrad (x k), x (k + 1)⟫ + L * V (x k) (x (k + 1)) + h (x (k + 1)) ≤
        ⟪fGrad (x k), u⟫ + L * V (x k) u + h u)
    (hgX : ∀ k, 1 ≤ k → k ≤ N → gX k = L • (x k - x (k + 1)))
    (R : ℕ) (hR : 1 ≤ R ∧ R ≤ N) (hRmin : ∀ k, 1 ≤ k → k ≤ N → ‖gX R‖ ≤ ‖gX k‖)
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f (x 1) + h (x 1) - ΨStar) / L)),
    ‖gX R‖ ^ 2 ≤ (2 * L ^ 2 * DΨ ^ 2) / (N : ℝ)) := by
  intro H
  have hglb : IsGLB ((fun x : ℝ => (0 : ℝ) + 0) '' Set.univ) 0 := by
    have e : ((fun x : ℝ => (0 : ℝ) + 0) '' Set.univ) = {0} := by ext; simp
    rw [e]; exact isGLB_singleton
  have := H (E := ℝ) Set.univ (fun _ => 0) (fun _ => 0) (fun _ _ => 0) 1 one_pos (fun _ => 0)
    (fun x _ y _ => by simp; positivity) 1 le_rfl (fun k => (k : ℝ))
    (fun k => (1 : ℝ) • ((k : ℝ) - ((k + 1 : ℕ) : ℝ))) (fun _ => trivial)
    (fun k _ _ u _ => by simp) (fun k _ _ => rfl) 1 ⟨le_rfl, le_rfl⟩
    (fun k hk1 hk2 => by rw [show k = 1 by omega]) 0 hglb 0 (by simp)
  norm_num at this
