-- Prove2me | solution 1 for BookProof.ChapterEulerStochastic.isProbVec_e1
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:52:52.796824+00:00
-- url     : https://prove2.me/submissions/bf59011e-64d4-4637-8f4d-6d3435d4dc19

-- Generated from ChapterEulerStochastic.lean — solution of BookProof.ChapterEulerStochastic.isProbVec_e1
import Mathlib
import Definitions.Def_ChapterEulerStochastic
open BookProof.ChapterEulerStochastic



open scoped Matrix BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : IsProbVec ![0, 1] := by

  exact ⟨ fun i => by fin_cases i <;> norm_num, by norm_num ⟩
