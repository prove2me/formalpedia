-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.one_sub_thermalRatio
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:33:25.722982+00:00
-- url     : https://prove2.me/submissions/c2c1627b-840e-433d-93ff-527337179093

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.one_sub_thermalRatio
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) : 1 - thermalRatio nbar = 1 / (nbar + 1) := by

  rw [thermalRatio]
  field_simp
  ring
