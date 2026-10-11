-- Prove2me | solution 1 for BookProof.ChapterParityHypercharge.hyperPhase_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:58.840526+00:00
-- url     : https://prove2.me/submissions/6816cb2c-91e8-446d-b39c-675c8452e7a7

-- Generated from ChapterParityHypercharge.lean — solution of BookProof.ChapterParityHypercharge.hyperPhase_neg_mul
import Mathlib
import Definitions.Def_ChapterParityHypercharge
import Theorems.Thm_BookProof_ChapterParityHypercharge_hyperPhase_zero
import Theorems.Thm_BookProof_ChapterParityHypercharge_hyperPhase_add
import Definitions.Def_ChapterA3
open BookProof.ChapterParityHypercharge



open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℝ) : hyperPhase θ * hyperPhase (-θ) = 1 := by

  rw [hyperPhase_add, add_neg_cancel, hyperPhase_zero]
