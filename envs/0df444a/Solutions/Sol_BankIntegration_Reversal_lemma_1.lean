-- Prove2me | solution 1 for BankIntegration.Reversal.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:19:14.830181+00:00
-- url     : https://prove2.me/submissions/b6c8f6b5-c095-459d-9555-a9ab80848af1

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model
import Theorems.Thm_BankIntegration_Reversal_lemma_6a

open BankIntegration.Reversal in
theorem solution (lam aj bj : ℝ) (n : ℕ) (hlam : 1 < lam) (ha : 0 < aj) (hb : 0 < bj)
    (hn : 1 ≤ n) :
    (∃! L : Fin n → ℝ, IsCournotEq lam 0 aj bj n L) ∧
    ∀ L : Fin n → ℝ, IsCournotEq lam 0 aj bj n L →
      (∀ i, ∑ k, L k = (n : ℝ) * L i) ∧
      depositRate aj (∑ k, L k) =
        lam * (((n : ℝ) + 1) / ((n : ℝ) + 2)) * (xi aj bj / (1 + xi aj bj)) ∧
      loanRate lam bj (∑ k, L k) =
        lam * (1 - ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1 / (1 + xi aj bj))) ∧
      ∀ θ : ℝ, IsOptimalRisk lam (loanRate lam bj (∑ k, L k)) θ ↔
        θ = lam * (1 - 1 / 2 * (((n : ℝ) + 1) / ((n : ℝ) + 2)) * (1 / (1 + xi aj bj))) := by
  obtain ⟨hex, hall⟩ := lemma_6a lam 0 aj bj n hlam le_rfl (by linarith) ha hb hn
  refine ⟨hex, fun L hL => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hall L hL
  refine ⟨h1, by rw [h2]; ring, by rw [h3]; ring, fun θ => ?_⟩
  rw [h4 θ]
  constructor <;> intro h <;> rw [h] <;> ring
