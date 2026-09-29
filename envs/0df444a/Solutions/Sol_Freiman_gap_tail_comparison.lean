-- Prove2me | solution 1 for Freiman.gap_tail_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:40:41.899617+00:00
-- url     : https://prove2.me/submissions/fae7fa84-2ad9-46a6-9563-31900ae06250

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_order_comparison
import Theorems.Thm_Freiman_gap_tail_first_difference

open Freiman

theorem solution (b c : ℕ → ℕ+) : ((∀ n, gapSameBefore b c n → gapUpperDigit b c n) → cfValue b ≤ cfValue c) ∧ ((∀ n, gapSameBefore b c n → gapLowerDigit b c n) → cfValue c ≤ cfValue b) := by
  exact gap_order_comparison gap_tail_first_difference b c
