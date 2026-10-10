-- Prove2me | solution 1 for BookProof.ChapterParityHypercharge.hyperPhase_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:13:06.482613+00:00
-- url     : https://prove2.me/submissions/ac231312-f48e-4c53-bc09-f3edb1ac3819

-- Generated from ChapterParityHypercharge.lean — solution of BookProof.ChapterParityHypercharge.hyperPhase_comm
import Mathlib
import Definitions.Def_ChapterParityHypercharge
import Definitions.Def_ChapterA3
open BookProof.ChapterParityHypercharge



open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℝ) : hyperPhase θ * mgamma5 = mgamma5 * hyperPhase θ := by

  unfold hyperPhase; simp [mul_add, add_mul]
