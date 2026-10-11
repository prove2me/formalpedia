-- Prove2me | solution 1 for BookProof.ChapterThermalMaxEntropy.thermalProb_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:18.270891+00:00
-- url     : https://prove2.me/submissions/246380f0-7849-438b-99e4-9b2cd454d9ce

-- Generated from ChapterThermalMaxEntropy.lean — solution of BookProof.ChapterThermalMaxEntropy.thermalProb_pos
import Mathlib
import Definitions.Def_ChapterThermalMaxEntropy
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterThermalMaxEntropy



noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 < nbar) (n : ℕ) : 0 < thermalProb nbar n := by

  have h1 : 0 < nbar + 1 := by linarith
  have hr : 0 < thermalRatio nbar := div_pos h h1
  exact mul_pos (by positivity) (pow_pos hr n)
