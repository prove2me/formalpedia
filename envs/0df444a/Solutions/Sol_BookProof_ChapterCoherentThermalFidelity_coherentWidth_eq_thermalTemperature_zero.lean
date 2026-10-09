-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.coherentWidth_eq_thermalTemperature_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:36:21.441993+00:00
-- url     : https://prove2.me/submissions/e8658e09-be1d-494d-951b-b7097980933d

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.coherentWidth_eq_thermalTemperature_zero
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
open BookProof.ChapterCoherentThermalFidelity



noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

variable {nbar lam : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution :
    coherentWidth = thermalTemperature 0 := by

  rw [coherentWidth, thermalTemperature]; norm_num
