-- Prove2me | solution 1 for Freiman.gap_minimum_left_initial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:26:58.001087+00:00
-- url     : https://prove2.me/submissions/ddfed1bd-d5a9-4950-adde-df32704e1d05

import Definitions.Def_Freiman_gapModel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Freiman

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMinimumAdmissible a) (hs : gapMatch a 0 gapSeedB) (n : ℕ) (hn : n < 4) (hp : gapSameBefore (gapLeftTail a) gapBLeft n) : gapLowerDigit (gapLeftTail a) gapBLeft n := by
  interval_cases n
  · have he := hs.2 4 (by decide)
    norm_num [gapSeedB] at he
    have he' : gapLeftTail a 0 = gapBLeft 0 := by
      simpa [gapLeftTail, gapBLeft, gapEventuallyPeriodic] using he
    unfold gapLowerDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 3 (by decide)
    norm_num [gapSeedB] at he
    have he' : gapLeftTail a 1 = gapBLeft 1 := by
      simpa [gapLeftTail, gapBLeft, gapEventuallyPeriodic] using he
    unfold gapLowerDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 2 (by decide)
    norm_num [gapSeedB] at he
    have he' : gapLeftTail a 2 = gapBLeft 2 := by
      simpa [gapLeftTail, gapBLeft, gapEventuallyPeriodic] using he
    unfold gapLowerDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 1 (by decide)
    norm_num [gapSeedB] at he
    have he' : gapLeftTail a 3 = gapBLeft 3 := by
      simpa [gapLeftTail, gapBLeft, gapEventuallyPeriodic] using he
    unfold gapLowerDigit
    rw [he']
    split_ifs <;> exact le_rfl

