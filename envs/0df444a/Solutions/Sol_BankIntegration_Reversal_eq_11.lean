-- Prove2me | solution 1 for BankIntegration.Reversal.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:19:16.147276+00:00
-- url     : https://prove2.me/submissions/a4ede5d1-1e44-4caa-888c-9fbf63219810

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model
import Theorems.Thm_BankIntegration_Reversal_lemma_1
import Theorems.Thm_BankIntegration_Reversal_lemma_2

open BankIntegration.Reversal in
theorem solution (lam a1 a2 b1 b2 : ℝ) (n : ℕ) (hS : Standing lam a1 a2 b1 b2 n)
    (L1 L2 : Fin n → ℝ) (LI : Fin (2 * n) → ℝ)
    (h1 : IsCournotEq lam 0 a1 b1 n L1) (h2 : IsCournotEq lam 0 a2 b2 n L2)
    (hI : IsCournotEq lam 0 (a1 + a2) (b1 + b2) (2 * n) LI) :
    loanRate lam (b1 + b2) (∑ i, LI i) - loanRate lam b1 (∑ i, L1 i) =
        bankCompetitorEffect lam n (xiStar a1 a2 b1 b2) +
          bankCustomerEffect lam n (xi a1 b1) (xiStar a1 a2 b1 b2) ∧
      loanRate lam (b1 + b2) (∑ i, LI i) - loanRate lam b2 (∑ i, L2 i) =
        bankCompetitorEffect lam n (xiStar a1 a2 b1 b2) +
          bankCustomerEffect lam n (xi a2 b2) (xiStar a1 a2 b1 b2) := by
  obtain ⟨hlam, ha1, ha2, hb1, hb2, hn⟩ := hS
  have r1 := ((lemma_1 lam a1 b1 n hlam ha1 hb1 hn).2 L1 h1).2.2.1
  have r2 := ((lemma_1 lam a2 b2 n hlam ha2 hb2 hn).2 L2 h2).2.2.1
  have rI := ((lemma_2 lam a1 a2 b1 b2 n ⟨hlam, ha1, ha2, hb1, hb2, hn⟩).2.1 LI hI).2.2.1
  rw [r1, r2, rI]
  unfold bankCompetitorEffect bankCustomerEffect
  constructor <;> ring
