-- Prove2me | solution 1 for BookProof.ChapterB4.P1_isPureState
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:45:17.911061+00:00
-- url     : https://prove2.me/submissions/120cfb0e-3bec-4894-b59e-56773ebaaa0a

-- Generated from ChapterB4.lean — solution of BookProof.ChapterB4.P1_isPureState
import Mathlib
import Definitions.Def_ChapterB4
open BookProof.ChapterB4




open Matrix

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : IsPureState P1 := by

  refine ⟨![1, 0], by norm_num, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P1]
