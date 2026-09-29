-- Prove2me | solution 1 for Freiman.gap_minimum_right_initial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:24:08.577625+00:00
-- url     : https://prove2.me/submissions/7fbff14a-db19-4623-8a4f-82f8a310a92d

import Definitions.Def_Freiman_gapModel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Freiman

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) (n : ℕ) (hn : n < 4) (hp : gapSameBefore (gapRightTail a) gapBRight n) : gapLowerDigit (gapRightTail a) gapBRight n := by
  interval_cases n
  · have he := hs.2 6 (by decide)
    norm_num [gapSeedB] at he
    have he' : gapRightTail a 0 = gapBRight 0 := by
      simpa [gapRightTail, gapBRight, gapEventuallyPeriodic] using he
    unfold gapLowerDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 7 (by decide)
    norm_num [gapSeedB] at he
    have he' : gapRightTail a 1 = gapBRight 1 := by
      simpa [gapRightTail, gapBRight, gapEventuallyPeriodic] using he
    unfold gapLowerDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 8 (by decide)
    norm_num [gapSeedB] at he
    have he' : gapRightTail a 2 = gapBRight 2 := by
      simpa [gapRightTail, gapBRight, gapEventuallyPeriodic] using he
    unfold gapLowerDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 9 (by decide)
    norm_num [gapSeedB] at he
    have he' : gapRightTail a 3 = gapBRight 3 := by
      simpa [gapRightTail, gapBRight, gapEventuallyPeriodic] using he
    unfold gapLowerDigit
    rw [he']
    split_ifs <;> exact le_rfl

