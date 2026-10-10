-- Prove2me | solution 1 for BookProof.ChapterIrreversible.le_one_of_prob
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:14:26.370339+00:00
-- url     : https://prove2.me/submissions/31f9d36c-0a2b-495d-b3cd-72c6c549866e

-- Generated from ChapterIrreversible.lean — solution of BookProof.ChapterIrreversible.le_one_of_prob
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin n → ℝ) (hnn : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (a : Fin n) : p a ≤ 1 := by

  exact hsum ▸ Finset.single_le_sum ( fun a _ => hnn a ) ( Finset.mem_univ a )
