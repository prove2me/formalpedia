-- Prove2me | solution 1 for BookProof.SpinStatistics.fermi_CAR_cross
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:49.6148+00:00
-- url     : https://prove2.me/submissions/32397b4d-4cc4-4dcb-a202-069c2bffa0e9

-- Generated from ChapterSpinStatistics.lean — solution of BookProof.SpinStatistics.fermi_CAR_cross
import Mathlib
import Definitions.Def_ChapterSpinStatistics
import Theorems.Thm_BookProof_SpinStatistics_fermiCreate2_eq
open BookProof.SpinStatistics




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : fermiAnnih1 * fermiCreate2 + fermiCreate2 * fermiAnnih1 = 0 := by

  rw [fermiCreate2_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [fermiAnnih1]
