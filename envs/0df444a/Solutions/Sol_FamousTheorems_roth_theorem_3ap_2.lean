-- Prove2me | solution 2 for FamousTheorems.roth_theorem_3ap
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:57:48.942783+00:00
-- url     : https://prove2.me/submissions/a4250f39-407d-4e94-9f33-071d6f4122f6

import Mathlib

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℕ, A ⊆ Finset.range n → ε * n ≤ A.card → ¬ ThreeAPFree (A : Set ℕ) :=
  ⟨cornersTheoremBound (ε / 3), fun _ hn A hA hAε => roth_3ap_theorem_nat ε hε hn A hA hAε⟩
