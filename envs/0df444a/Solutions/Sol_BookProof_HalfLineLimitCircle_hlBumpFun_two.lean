-- Prove2me | solution 1 for BookProof.HalfLineLimitCircle.hlBumpFun_two
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:41:11.797979+00:00
-- url     : https://prove2.me/submissions/066e4c5a-5ee5-4be7-aa9a-4d7407b11c0c

-- Generated from ChapterHalfLineLimitCircle.lean — solution of BookProof.HalfLineLimitCircle.hlBumpFun_two
import Mathlib
import Definitions.Def_ChapterHalfLineLimitCircle
import Definitions.Def_ChapterFarisLavine
open BookProof.HalfLineLimitCircle




open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

set_option maxHeartbeats 1000000 in
theorem solution : hlBumpFun 2 = 1 := by

  have h : hlBump 2 = 1 :=
    hlBump.one_of_mem_closedBall (by simp [Metric.mem_closedBall]; norm_num [hlBump])
  simp [hlBumpFun, h]
