-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiCreate2_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:16.096369+00:00
-- url     : https://prove2.me/submissions/4b1e47cb-1db8-4533-b8b4-93760d0fbe91

-- Generated from ChapterSpinStatistics.lean — solution of BookProof.SpinStatistics.fermiCreate2_eq
import Mathlib
import Definitions.Def_ChapterSpinStatistics
open BookProof.SpinStatistics




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : fermiCreate2 = !![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,-1,0] := by

  ext i j; fin_cases i <;> fin_cases j <;>
    simp [fermiCreate2, fermiAnnih2, Matrix.conjTranspose_apply]
