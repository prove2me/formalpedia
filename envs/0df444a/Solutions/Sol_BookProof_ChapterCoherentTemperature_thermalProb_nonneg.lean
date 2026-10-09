-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.thermalProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:33:26.70183+00:00
-- url     : https://prove2.me/submissions/842390b1-107e-46d5-8c88-eef35467e763

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.thermalProb_nonneg
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
import Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalRatio_nonneg
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) (n : ℕ) : 0 ≤ thermalProb nbar n := mul_nonneg (by positivity) (pow_nonneg (thermalRatio_nonneg h) n)
