-- Prove2me | solution 1 for BookProof.ChapterThermalMaxEntropy.log_thermalProb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:19.64925+00:00
-- url     : https://prove2.me/submissions/26c606da-98fa-43e3-a788-f5e6f65bfd9c

-- Generated from ChapterThermalMaxEntropy.lean — solution of BookProof.ChapterThermalMaxEntropy.log_thermalProb
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
theorem solution (h : 0 < nbar) (n : ℕ) :
    Real.log (thermalProb nbar n)
      = -Real.log (nbar + 1) + (n : ℝ) * Real.log (thermalRatio nbar) := by

  have h1 : 0 < nbar + 1 := by linarith
  have hr : 0 < thermalRatio nbar := div_pos h h1
  rw [thermalProb, Real.log_mul (by positivity) (by positivity), Real.log_pow, one_div,
    Real.log_inv]
