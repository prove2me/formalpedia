-- Prove2me | solution 1 for BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:21.002993+00:00
-- url     : https://prove2.me/submissions/41af751c-d83c-4630-90d7-6ecbe5774965

-- Generated from ChapterThermalMaxEntropy.lean — solution of BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq
import Mathlib
import Definitions.Def_ChapterThermalMaxEntropy
import Theorems.Thm_BookProof_ChapterThermalMaxEntropy_log_thermalProb
import Theorems.Thm_BookProof_ChapterCoherentOccupation_thermalProb_mul_summable
import Theorems.Thm_BookProof_ChapterCoherentOccupation_thermalProb_summable
import Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalProb_mean
import Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalProb_tsum_one
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
theorem solution (h : 0 < nbar) :
    thermalEntropy nbar = Real.log (nbar + 1) - nbar * Real.log (thermalRatio nbar) := by

  have h0 : (0 : ℝ) ≤ nbar := le_of_lt h
  have sP := thermalProb_summable h0
  have sN := thermalProb_mul_summable h0
  have hf : ∀ n : ℕ, thermalProb nbar n * Real.log (thermalProb nbar n)
      = (-Real.log (nbar + 1)) * thermalProb nbar n
        + Real.log (thermalRatio nbar) * ((n : ℝ) * thermalProb nbar n) := by
    intro n; rw [log_thermalProb h n]; ring
  rw [thermalEntropy, tsum_congr hf,
    Summable.tsum_add (sP.mul_left _) (sN.mul_left _), sP.tsum_mul_left, sN.tsum_mul_left,
    thermalProb_tsum_one h0, thermalProb_mean h0]
  ring
