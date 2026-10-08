-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiAnnih1_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:07:19.758933+00:00
-- url     : https://prove2.me/submissions/9a9549c2-f621-4401-96fa-9b6c10b41b62

-- Generated from ChapterSpinStatistics.lean — solution of BookProof.SpinStatistics.fermiAnnih1_sq
import Mathlib
import Definitions.Def_ChapterSpinStatistics
open BookProof.SpinStatistics




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : fermiAnnih1 * fermiAnnih1 = 0 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [fermiAnnih1]
