-- Prove2me | solution 1 for BookProof.SpinStatistics.fermi_CAR_cross_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:40.799766+00:00
-- url     : https://prove2.me/submissions/3feb5a2e-0d1e-4790-bafd-fd30e8d5dae0

-- Generated from ChapterSpinStatistics.lean — solution of BookProof.SpinStatistics.fermi_CAR_cross'
import Mathlib
import Definitions.Def_ChapterSpinStatistics
import Theorems.Thm_BookProof_SpinStatistics_fermiCreate1_eq
open BookProof.SpinStatistics




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : fermiAnnih2 * fermiCreate1 + fermiCreate1 * fermiAnnih2 = 0 := by

  rw [fermiCreate1_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [fermiAnnih2]
