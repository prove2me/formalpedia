-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.thermalRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:33:11.006657+00:00
-- url     : https://prove2.me/submissions/1432ae8a-0e07-4e45-b37f-02b6c33f284e

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.thermalRatio_lt_one
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
import Theorems.Thm_BookProof_ChapterCoherentTemperature_nbar_add_one_pos
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) : thermalRatio nbar < 1 := by

  rw [thermalRatio, div_lt_one (nbar_add_one_pos h)]
  linarith
