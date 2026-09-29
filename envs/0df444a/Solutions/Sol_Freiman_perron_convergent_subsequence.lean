-- Prove2me | solution 1 for Freiman.perron_convergent_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:17.568145+00:00
-- url     : https://prove2.me/submissions/bb564bc5-97a8-4afe-bfe1-323901303c8d

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_continuant_eventually_nearest
import Theorems.Thm_Freiman_perron_inverse_error

open Freiman

theorem solution (b : ℕ → ℕ+) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      approximationValue (cfValue b) (continuantQ b n) = perronValue b n := by
  obtain ⟨N, hN⟩ := continuant_eventually_nearest b
  refine ⟨N, ?_⟩
  intro n hn
  rw [approximationValue, hN n hn]
  exact perron_inverse_error b n
