-- Prove2me | solution 1 for BookProof.ChapterLinftyMultiplication.multOp_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:37:37.244209+00:00
-- url     : https://prove2.me/submissions/b89dcf84-4d84-45c4-81a9-7c61ae192d3e

-- Generated from ChapterLinftyMultiplication.lean — solution of BookProof.ChapterLinftyMultiplication.multOp_one
import Mathlib
import Definitions.Def_ChapterLinftyMultiplication
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_memLp_top_one
open BookProof.ChapterLinftyMultiplication



noncomputable section

open MeasureTheory ENNReal Complex


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution : multOp (fun _ : α => (1 : ℂ)) memLp_top_one
    = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by

  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [multOp_coeFn (fun _ : α => (1 : ℂ)) memLp_top_one f] with x h1
  simp [h1]
