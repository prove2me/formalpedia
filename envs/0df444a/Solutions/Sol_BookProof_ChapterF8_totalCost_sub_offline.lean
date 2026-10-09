-- Prove2me | solution 1 for BookProof.ChapterF8.totalCost_sub_offline
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:11:11.114842+00:00
-- url     : https://prove2.me/submissions/54a9bd3b-afca-4866-a0b1-39a0c05e788f

-- Generated from ChapterF8.lean — solution of BookProof.ChapterF8.totalCost_sub_offline
import Mathlib
import Definitions.Def_ChapterF8
open BookProof.ChapterF8



noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M d m K₂ k : ℕ) :
    totalCost M d m K₂ k - offlineCost M d k = onlineCost d m K₂ k := by

  rw [totalCost]
  omega
