-- Prove2me | solution 1 for BookProof.ChapterShannonSampling.half_add_period
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:31:06.690259+00:00
-- url     : https://prove2.me/submissions/02f758d9-ad68-4bda-b6e1-0d306fc5ae7c

-- Generated from ChapterShannonSampling.lean — solution of BookProof.ChapterShannonSampling.half_add_period
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling




open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

set_option maxHeartbeats 1000000 in
omit hT in
theorem solution : -(T / 2) + T = T / 2 := by
 ring
