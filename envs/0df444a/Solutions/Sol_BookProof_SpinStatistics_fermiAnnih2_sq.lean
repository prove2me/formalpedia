-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiAnnih2_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:07:31.128983+00:00
-- url     : https://prove2.me/submissions/108a99c7-9c91-47db-9c51-3d6e4fe41263

-- Generated from ChapterSpinStatistics.lean — solution of BookProof.SpinStatistics.fermiAnnih2_sq
import Mathlib
import Definitions.Def_ChapterSpinStatistics
open BookProof.SpinStatistics




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : fermiAnnih2 * fermiAnnih2 = 0 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [fermiAnnih2]
