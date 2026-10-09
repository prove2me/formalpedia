-- Prove2me | solution 1 for BookProof.ChapterBoseEinstein.boseEinstein_mean
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:33:01.545135+00:00
-- url     : https://prove2.me/submissions/1f605743-928a-4c5d-aee9-8cb064772d6d

-- Generated from ChapterBoseEinstein.lean — solution of BookProof.ChapterBoseEinstein.boseEinstein_mean
import Mathlib
import Definitions.Def_ChapterBoseEinstein
import Theorems.Thm_BookProof_ChapterBoseEinstein_boseEinstein_pos
import Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalProb_mean
open BookProof.ChapterBoseEinstein



noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

variable {x : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hx : 0 < x) :
    ∑' n : ℕ, (n : ℝ) * thermalProb (boseEinstein x) n = boseEinstein x := thermalProb_mean (le_of_lt (boseEinstein_pos hx))
