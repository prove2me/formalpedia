-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.thermalTemperature_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:34:58.386972+00:00
-- url     : https://prove2.me/submissions/2b7649d1-cfe8-4cdd-a6b4-57c050fcff68

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.thermalTemperature_strictMono
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution : StrictMono thermalTemperature := by

  intro a b hab
  simpa [thermalTemperature] using hab
