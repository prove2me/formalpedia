-- Prove2me | solution 1 for Freiman.gap_minimum_left_tail
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:43:29.770261+00:00
-- url     : https://prove2.me/submissions/a9bfc404-b4fe-43af-adc0-4476a30ff262

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_minimum_left_initial
import Theorems.Thm_Freiman_gap_minimum_left_period
import Theorems.Thm_Freiman_gap_tail_comparison

open Freiman

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) : cfValue (gapLeftTail a) ≥ cfValue gapBLeft := by
  apply (gap_tail_comparison (gapLeftTail a) gapBLeft).2
  intro n hp
  by_cases hn : n < 4
  · exact gap_minimum_left_initial a hd ha hs n hn hp
  · have heq : 4+6*((n-4)/6)+(n-4)%6 = n := by omega
    have h := gap_minimum_left_period a hd ha hs ((n-4)/6) ((n-4)%6) (Nat.mod_lt _ (by decide))
    simpa only [heq] using h (by simpa only [heq] using hp)
