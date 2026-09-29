-- Prove2me | solution 1 for Freiman.gap_maximum_left_tail
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:43:29.967035+00:00
-- url     : https://prove2.me/submissions/78f290e5-d359-4c29-a372-71b8837e62b7

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_maximum_left_initial
import Theorems.Thm_Freiman_gap_maximum_left_period
import Theorems.Thm_Freiman_gap_tail_comparison

open Freiman

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) : cfValue (gapLeftTail a) ≤ cfValue gapALeft := by
  apply (gap_tail_comparison (gapLeftTail a) gapALeft).1
  intro n hp
  by_cases hn : n < 14
  · exact gap_maximum_left_initial a hd ha hs n hn hp
  · have heq : 14+6*((n-14)/6)+(n-14)%6 = n := by omega
    have h := gap_maximum_left_period a hd ha hs ((n-14)/6) ((n-14)%6) (Nat.mod_lt _ (by decide))
    simpa only [heq] using h (by simpa only [heq] using hp)
