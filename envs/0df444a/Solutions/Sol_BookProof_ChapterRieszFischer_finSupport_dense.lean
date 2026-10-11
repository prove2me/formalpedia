-- Prove2me | solution 1 for BookProof.ChapterRieszFischer.finSupport_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:44.314151+00:00
-- url     : https://prove2.me/submissions/d07aca1a-c9f4-467d-803f-20fd62ef8ea4

-- Generated from ChapterRieszFischer.lean — solution of BookProof.ChapterRieszFischer.finSupport_dense
import Mathlib
import Definitions.Def_ChapterRieszFischer
import Theorems.Thm_BookProof_ChapterRieszFischer_riesz_fischer_hasSum
import Theorems.Thm_BookProof_ChapterRieszFischer_sum_single_mem_finSupport
open BookProof.ChapterRieszFischer



open Filter
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution : Dense FinSupport := by

  intro f
  refine mem_closure_of_tendsto (riesz_fischer_hasSum f) ?_
  filter_upwards with s using sum_single_mem_finSupport f s
