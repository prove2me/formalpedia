-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.nonconvex_md_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:21:12.234789+00:00
-- url     : https://prove2.me/submissions/2a35f016-fce1-45b6-b902-d43003b72c90

import Mathlib

open scoped RealInnerProductSpace

/-- Counterexample: nothing constrains `V` (the book's Bregman distance). With `V = 0`,
`f = h = 0` and `fGrad = 0` every point is a generalized projection, so the iterates
`x k = k` in `E = ℝ` are admissible. With `L = 1`, `N = 1`, `γ k = 1` and `R = 1` we get
`Ψ* = 0`, `DΨ = 0` and `‖gX 1‖² = 1`, while the claimed bound is `L·DΨ² / (1 - 1/2) = 0`. -/
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h : E → ℝ) (V : E → E → ℝ) (L : ℝ) (hL : 0 < L) (fGrad : E → E)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - ⟪fGrad x, y - x⟫ ≤ (L / 2) * ‖y - x‖ ^ 2)
    (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → E) (γ : ℕ → ℝ) (gX : ℕ → E)
    (hx : ∀ k, x k ∈ X)
    (hxDef : ∀ k, 1 ≤ k → k ≤ N → ∀ u ∈ X,
      ⟪fGrad (x k), x (k + 1)⟫ + (1 / γ k) * V (x k) (x (k + 1)) + h (x (k + 1)) ≤
        ⟪fGrad (x k), u⟫ + (1 / γ k) * V (x k) u + h u)
    (hgX : ∀ k, 1 ≤ k → k ≤ N → gX k = (1 / γ k) • (x k - x (k + 1)))
    (hγpos : ∀ k, 1 ≤ k → k ≤ N → 0 < γ k) (hγub : ∀ k, 1 ≤ k → k ≤ N → γ k ≤ 2 / L)
    (hγstrict : ∃ k, 1 ≤ k ∧ k ≤ N ∧ γ k < 2 / L)
    (R : ℕ) (hR : 1 ≤ R ∧ R ≤ N) (hRmin : ∀ k, 1 ≤ k → k ≤ N → ‖gX R‖ ≤ ‖gX k‖)
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f (x 1) + h (x 1) - ΨStar) / L)),
    ‖gX R‖ ^ 2 ≤ (L * DΨ ^ 2) / ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2 / 2)) := by
  intro H
  have hglb : IsGLB ((fun x : ℝ => (0 : ℝ) + 0) '' Set.univ) 0 := by
    have e : ((fun x : ℝ => (0 : ℝ) + 0) '' Set.univ) = {0} := by ext; simp
    rw [e]; exact isGLB_singleton
  have := H (E := ℝ) Set.univ (fun _ => 0) (fun _ => 0) (fun _ _ => 0) 1 one_pos (fun _ => 0)
    (fun x _ y _ => by simp; positivity) 1 le_rfl (fun k => (k : ℝ)) (fun _ => 1)
    (fun k => (1 / (1 : ℝ)) • ((k : ℝ) - ((k + 1 : ℕ) : ℝ))) (fun _ => trivial)
    (fun k _ _ u _ => by simp) (fun k _ _ => rfl) (fun _ _ _ => one_pos)
    (fun _ _ _ => by norm_num) ⟨1, le_rfl, le_rfl, by norm_num⟩ 1 ⟨le_rfl, le_rfl⟩
    (fun k hk1 hk2 => by rw [show k = 1 by omega]) 0 hglb 0 (by simp)
  norm_num at this
