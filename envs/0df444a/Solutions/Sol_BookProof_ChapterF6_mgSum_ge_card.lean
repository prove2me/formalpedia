-- Prove2me | solution 1 for BookProof.ChapterF6.mgSum_ge_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:05:47.482179+00:00
-- url     : https://prove2.me/submissions/d7f1b179-ea18-47cf-800a-adf802b8eb00

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgSum_ge_card
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (T : α →₀ ℕ) : T.support.card ≤ mgSum T := by

  exact Finset.card_eq_sum_ones _ ▸ Finset.sum_le_sum fun x hx => Nat.one_le_iff_ne_zero.mpr (
      Finsupp.mem_support_iff.mp hx )
