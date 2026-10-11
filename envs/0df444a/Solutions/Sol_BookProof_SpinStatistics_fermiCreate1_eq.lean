-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiCreate1_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:15.012985+00:00
-- url     : https://prove2.me/submissions/603fe595-34e1-489f-9655-b49afa4ccb00

-- Generated from ChapterSpinStatistics.lean — solution of BookProof.SpinStatistics.fermiCreate1_eq
import Mathlib
import Definitions.Def_ChapterSpinStatistics
open BookProof.SpinStatistics




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : fermiCreate1 = !![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0] := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [fermiCreate1, fermiAnnih1, Matrix.conjTranspose_apply]
