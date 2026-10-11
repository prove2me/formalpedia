-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiAnticomm_create
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:43.31805+00:00
-- url     : https://prove2.me/submissions/a8ed2672-b0dc-4cee-8175-c45a364ce6c9

-- Generated from ChapterSpinStatistics.lean — solution of BookProof.SpinStatistics.fermiAnticomm_create
import Mathlib
import Definitions.Def_ChapterSpinStatistics
import Theorems.Thm_BookProof_SpinStatistics_fermiCreate1_eq
import Theorems.Thm_BookProof_SpinStatistics_fermiCreate2_eq
open BookProof.SpinStatistics




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution :
    fermiCreate1 * fermiCreate2 + fermiCreate2 * fermiCreate1 = 0 := by

  rw [fermiCreate1_eq, fermiCreate2_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp
