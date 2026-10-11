-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.Jgen_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:07:02.50734+00:00
-- url     : https://prove2.me/submissions/078dd494-9f57-41a4-8ff5-0b66d11a4976

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.Jgen_sq
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution : Jgen * Jgen = -1 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [Jgen]
