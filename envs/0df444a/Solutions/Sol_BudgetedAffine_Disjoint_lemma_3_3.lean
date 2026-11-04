-- Prove2me | solution 1 for BudgetedAffine.Disjoint.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:02:34.46093+00:00
-- url     : https://prove2.me/submissions/d63a29b2-2a4e-47c0-a04f-e79992e01a65

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Theorems.Thm_BudgetedAffine_Budget_lemma_3_3

open Matrix

theorem solution :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (m : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
      (J : Finset (Fin m)) (γ : ℝ) (w : Fin m → ℝ),
      (∀ i j, 0 ≤ B i j) → 0 ≤ d → 0 < γ → (∀ i ∈ J, 0 < w i ∧ w i ≤ 1) →
      (∀ i ∈ J, ((4 * γ * (Real.log n / Real.log (Real.log n)) * w i : ℝ) : EReal) <
        BudgetedAffine.Budget.coverCost B d (Pi.single i 1)) →
      (∀ W ⊆ J, ∑ i ∈ W, w i ≤ 1 → BudgetedAffine.Budget.coverCost B d (BudgetedAffine.Budget.indic W) ≤ (γ : EReal)) →
      BudgetedAffine.Budget.coverCost B d (BudgetedAffine.Budget.indic J) ≤ ((4 * γ * (Real.log n / Real.log (Real.log n)) : ℝ) : EReal) :=
  BudgetedAffine.Budget.lemma_3_3
