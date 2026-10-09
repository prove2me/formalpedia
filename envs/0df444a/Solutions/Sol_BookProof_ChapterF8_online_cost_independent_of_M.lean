-- Prove2me | solution 1 for BookProof.ChapterF8.online_cost_independent_of_M
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:11:10.222604+00:00
-- url     : https://prove2.me/submissions/4bfce977-55ed-442a-8e49-b3ae72c434d8

-- Generated from ChapterF8.lean — solution of BookProof.ChapterF8.online_cost_independent_of_M
import Mathlib
import Definitions.Def_ChapterF8
open BookProof.ChapterF8



noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M M' d m K₂ k : ℕ) :
    totalCost M d m K₂ k + offlineCost M' d k
      = totalCost M' d m K₂ k + offlineCost M d k := by

  rw [totalCost, totalCost]
  omega
