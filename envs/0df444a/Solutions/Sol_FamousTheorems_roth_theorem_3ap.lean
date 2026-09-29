-- Prove2me | solution 1 for FamousTheorems.roth_theorem_3ap
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:56:28.807591+00:00
-- url     : https://prove2.me/submissions/970af860-2c64-4f6e-8e30-b457d37644bc

import Mathlib

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset ℕ, A ⊆ Finset.range n → ε * n ≤ A.card → ¬ ThreeAPFree (A : Set ℕ) :=
  ⟨cornersTheoremBound (ε / 3), fun _ hn A hA hAε => roth_3ap_theorem_nat ε hε hn A hA hAε⟩
