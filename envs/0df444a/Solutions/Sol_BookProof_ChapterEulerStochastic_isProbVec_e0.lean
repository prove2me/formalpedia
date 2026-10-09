-- Prove2me | solution 1 for BookProof.ChapterEulerStochastic.isProbVec_e0
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:52:51.711297+00:00
-- url     : https://prove2.me/submissions/d24a2783-fe8f-4415-849a-acd0879054d7

-- Generated from ChapterEulerStochastic.lean — solution of BookProof.ChapterEulerStochastic.isProbVec_e0
import Mathlib
import Definitions.Def_ChapterEulerStochastic
open BookProof.ChapterEulerStochastic



open scoped Matrix BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : IsProbVec ![1, 0] := by

  exact ⟨ fun i => by fin_cases i <;> norm_num, by norm_num ⟩
