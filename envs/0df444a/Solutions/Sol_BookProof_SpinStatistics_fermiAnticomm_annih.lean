-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiAnticomm_annih
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:42.055979+00:00
-- url     : https://prove2.me/submissions/3068733e-c6b0-419a-a5f6-62a7dc9633e9

-- Generated from ChapterSpinStatistics.lean — solution of BookProof.SpinStatistics.fermiAnticomm_annih
import Mathlib
import Definitions.Def_ChapterSpinStatistics
open BookProof.SpinStatistics




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : fermiAnnih1 * fermiAnnih2 + fermiAnnih2 * fermiAnnih1 = 0 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [fermiAnnih1, fermiAnnih2]
