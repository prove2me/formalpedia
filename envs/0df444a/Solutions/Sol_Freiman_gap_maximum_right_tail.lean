-- Prove2me | solution 1 for Freiman.gap_maximum_right_tail
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:43:29.869003+00:00
-- url     : https://prove2.me/submissions/44d413b3-87d0-48a4-88df-fcc7c698f8b4

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_maximum_right_initial
import Theorems.Thm_Freiman_gap_maximum_right_period
import Theorems.Thm_Freiman_gap_tail_comparison

open Freiman

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) : cfValue (gapRightTail a) ≤ cfValue gapARight := by
  apply (gap_tail_comparison (gapRightTail a) gapARight).1
  intro n hp
  by_cases hn : n < 7
  · exact gap_maximum_right_initial a hd ha hs n hn hp
  · have heq : 7+6*((n-7)/6)+(n-7)%6 = n := by omega
    have h := gap_maximum_right_period a hd ha hs ((n-7)/6) ((n-7)%6) (Nat.mod_lt _ (by decide))
    simpa only [heq] using h (by simpa only [heq] using hp)
