-- Prove2me | solution 1 for ExactDFTRefine.Main.beta_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:27:54.083846+00:00
-- url     : https://prove2.me/submissions/06bb82d2-eb8f-4792-891e-8f042c79b1b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ExactDFTRefine_Main_separated_P16A8Z_fourier_transfer
import Theorems.Thm_ExactDFTRefine_Main_proposition_4_2

open ExactDFTRefine.Main

theorem solution :
    delta < beta ∧ beta < Cpar ∧
    ∃ (P₁ P₂ : Program) (c : ℕ) (K : ℝ) (n₀ : ℕ), 0 < K ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x : Fin n → ℂ, ∃ W : ℕ, DFTRun P₁ P₂ c n x W ∧
        (n₀ ≤ n → (W : ℝ) ≤
          K * n * Real.log (n : ℝ) ^ (1 - beta) * Real.log (Real.log (n : ℝ)) ^ 2) := by
  refine ⟨by norm_num [delta, beta], by norm_num [beta, Cpar], ?_⟩
  obtain ⟨hmoment, hsep⟩ := proposition_4_2
  exact separated_P16A8Z_fourier_transfer beta (by norm_num [beta])
    (by norm_num [beta, Cpar]) hmoment hsep