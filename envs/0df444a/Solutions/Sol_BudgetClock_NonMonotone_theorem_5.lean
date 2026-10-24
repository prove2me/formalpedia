-- Prove2me | solution 1 for BudgetClock.NonMonotone.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:40:01.765278+00:00
-- url     : https://prove2.me/submissions/9d4b4583-e78a-48f2-b082-493b99f12467

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_NonMonotone_Mechanism
import Theorems.Thm_BudgetClock_NonMonotone_budget_feasible
import Theorems.Thm_BudgetClock_NonMonotone_pruning_step
import Theorems.Thm_BudgetClock_NonMonotone_lemma_7

open BudgetClock.NonMonotone

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (usm : Finset (Fin n) → Finset (Fin n))
    (husm : ∀ X, usm X ⊆ X ∧ ∀ Y ⊆ X, v Y ≤ 2 * v (usm X)) :
    (∑ i ∈ (simultaneousIterativePruning v c B usm).1,
        (simultaneousIterativePruning v c B usm).2 i ≤ B) ∧
      ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
        v O ≤ 64 * v (simultaneousIterativePruning v c B usm).1 := by
  refine ⟨budget_feasible v hv hsub c hc B hB usm husm, fun O hO => ?_⟩
  obtain ⟨L, hL, h7⟩ := lemma_7 v hv hsub c hc B hB usm husm O hO
  have hp := pruning_step v hv hsub c hc B hB usm husm L hL
  linarith
