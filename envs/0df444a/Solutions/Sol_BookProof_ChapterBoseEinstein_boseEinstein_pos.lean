-- Prove2me | solution 1 for BookProof.ChapterBoseEinstein.boseEinstein_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:32:44.96812+00:00
-- url     : https://prove2.me/submissions/2efd8493-a715-415c-90f7-0462c1d29756

-- Generated from ChapterBoseEinstein.lean — solution of BookProof.ChapterBoseEinstein.boseEinstein_pos
import Mathlib
import Definitions.Def_ChapterBoseEinstein
import Theorems.Thm_BookProof_ChapterBoseEinstein_exp_sub_one_pos
open BookProof.ChapterBoseEinstein



noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

variable {x : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hx : 0 < x) : 0 < boseEinstein x := div_pos one_pos (exp_sub_one_pos hx)
