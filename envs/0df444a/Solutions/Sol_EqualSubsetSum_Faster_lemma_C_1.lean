-- Prove2me | solution 1 for EqualSubsetSum.Faster.lemma_C_1
-- status  : ACCEPTED   (disprove)
-- author  : @Xeroth
-- created : 2026-11-22T20:42:24.696345+00:00
-- url     : https://prove2.me/submissions/ab0f91a5-1057-4dde-8ccf-4e6a8890260c

import Mathlib

/-- Disproof of `EqualSubsetSum.Faster.lemma_C_1`: with `ι = Empty`, `c₁ = -1`, `c₂ = 1`,
`N = 0`, `K = {0}`, `Par = {0, 1} ⊆ ℝ^1`, all hypotheses hold but the conclusion asks for a
negative distance. -/
theorem solution : ¬ (∀ {N M : ℕ} {ι : Type} [Fintype ι]
    (K : Set (Fin N → ℝ)) (_hKc : IsCompact K) (_hKconv : Convex ℝ K)
    (_hK01 : K ⊆ Set.Icc (0 : Fin N → ℝ) 1)
    (Par : Set (Fin M → ℝ)) (L : ι → (Fin M → ℝ) → (Fin N → ℝ) → ℝ)
    (_hAff : ∀ l, ∀ a ∈ Par, ∃ f : (Fin N → ℝ) →ᵃ[ℝ] ℝ, ∀ x, L l a x = f x)
    (c₁ c₂ : ℝ)
    (_hLip : ∀ l, ∀ a ∈ Par, ∀ a' ∈ Par, ∀ x ∈ K, |L l a x - L l a' x| ≤ c₁ * ‖a - a'‖)
    (_hc₂ : 0 < c₂) (xStar : Fin N → ℝ) (_hxStar : xStar ∈ K)
    (_hStar : ∀ a ∈ Par, ∀ l, L l a xStar ≤ -c₂),
    (∀ a ∈ Par, ∀ a' ∈ Par, ∀ x ∈ K, (∀ l, L l a x ≤ 0) →
        ∃ x' ∈ K, (∀ l, L l a' x' ≤ 0) ∧ ‖x - x'‖ ≤ (c₁ / c₂) * ‖a - a'‖) ∧
    (∀ a ∈ Par, ∀ a' ∈ Par, ∀ x ∈ K, (∀ l, L l a' x ≤ 0) →
        ∃ x' ∈ K, (∀ l, L l a x' ≤ 0) ∧ ‖x - x'‖ ≤ (c₁ / c₂) * ‖a - a'‖)) := by
  intro h
  have key := (h (N := 0) (M := 1) (ι := Empty) {0} isCompact_singleton (convex_singleton 0)
    (by simp) {0, 1} (fun e => e.elim) (fun l => l.elim) (-1) 1 (fun l => l.elim) one_pos 0 rfl
    (fun _ _ l => l.elim)).1 0 (by simp) 1 (by simp) 0 rfl (fun l => l.elim)
  obtain ⟨x', -, -, hx⟩ := key
  have h1 : ‖(0 : Fin 1 → ℝ) - 1‖ = 1 := by simp
  have h2 := norm_nonneg ((0 : Fin 0 → ℝ) - x')
  rw [h1] at hx
  linarith
