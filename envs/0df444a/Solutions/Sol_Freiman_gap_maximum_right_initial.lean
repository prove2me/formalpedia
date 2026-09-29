-- Prove2me | solution 1 for Freiman.gap_maximum_right_initial
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:25:11.805371+00:00
-- url     : https://prove2.me/submissions/e8a3d9a3-029b-433a-8dee-0d1efd835c71

import Definitions.Def_Freiman_gapModel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Freiman

theorem solution (a : ℤ → ℕ+) (hd : gapDigits a) (ha : gapMaximumAdmissible a) (hs : gapMatch a 0 gapSeedA) (n : ℕ) (hn : n < 7) (hp : gapSameBefore (gapRightTail a) gapARight n) : gapUpperDigit (gapRightTail a) gapARight n := by
  interval_cases n
  · have he := hs.2 10 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapRightTail a 0 = gapARight 0 := by
      simpa [gapRightTail, gapARight, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 11 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapRightTail a 1 = gapARight 1 := by
      simpa [gapRightTail, gapARight, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 12 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapRightTail a 2 = gapARight 2 := by
      simpa [gapRightTail, gapARight, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 13 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapRightTail a 3 = gapARight 3 := by
      simpa [gapRightTail, gapARight, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 14 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapRightTail a 4 = gapARight 4 := by
      simpa [gapRightTail, gapARight, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 15 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapRightTail a 5 = gapARight 5 := by
      simpa [gapRightTail, gapARight, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl
  · have he := hs.2 16 (by decide)
    norm_num [gapSeedA] at he
    have he' : gapRightTail a 6 = gapARight 6 := by
      simpa [gapRightTail, gapARight, gapEventuallyPeriodic] using he
    unfold gapUpperDigit
    rw [he']
    split_ifs <;> exact le_rfl

