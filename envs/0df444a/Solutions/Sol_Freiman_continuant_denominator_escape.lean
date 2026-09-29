-- Prove2me | solution 1 for Freiman.continuant_denominator_escape
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:04.000792+00:00
-- url     : https://prove2.me/submissions/c54e9e6d-0494-4272-9a42-ef2be34089e3

import Definitions.Def_Freiman_continuants
import Theorems.Thm_Freiman_fibonacci_escape
import Theorems.Thm_Freiman_continuant_fibonacci

open Freiman

theorem solution (b : ℕ → ℕ+) :
    ∀ R : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R ≤ continuantQ b n := by
  intro R
  obtain ⟨N, hN⟩ := fibonacci_escape R
  refine ⟨N, ?_⟩
  intro n hn
  apply (hN n hn).trans
  simpa [continuantQ] using continuant_fibonacci ((List.range n).map b)
