-- Prove2me | solution 1 for BookProof.ChapterBoseEinstein.exp_sub_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:32:08.277896+00:00
-- url     : https://prove2.me/submissions/a37e6ff3-250e-47c9-96a9-cfa6a937c57f

-- Generated from ChapterBoseEinstein.lean — solution of BookProof.ChapterBoseEinstein.exp_sub_one_pos
import Mathlib
import Definitions.Def_ChapterBoseEinstein
open BookProof.ChapterBoseEinstein



noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

variable {x : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hx : 0 < x) : 0 < Real.exp x - 1 := by

  have := Real.add_one_lt_exp (ne_of_gt hx)
  linarith
