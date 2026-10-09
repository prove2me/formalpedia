-- Prove2me | solution 1 for BookProof.ChapterB4.P2_isPureState
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:45:13.751983+00:00
-- url     : https://prove2.me/submissions/54a3f28b-3cdb-4cfc-b886-8acb63b2a103

-- Generated from ChapterB4.lean — solution of BookProof.ChapterB4.P2_isPureState
import Mathlib
import Definitions.Def_ChapterB4
open BookProof.ChapterB4




open Matrix

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : IsPureState P2 := by

  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨![Real.sqrt 2 / 2, Real.sqrt 2 / 2], ?_, ?_⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [hmul]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [P2] <;> nlinarith [hmul]
