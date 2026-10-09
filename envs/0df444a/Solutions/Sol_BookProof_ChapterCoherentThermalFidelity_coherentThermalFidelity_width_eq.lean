-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_width_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:36:48.385993+00:00
-- url     : https://prove2.me/submissions/b4383aa0-6a9a-4da2-9857-193ba5ee7831

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_width_eq
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
theorem solution (nbar : ℝ) :
    nbar + 1 = thermalTemperature nbar + coherentWidth := by

  rw [thermalTemperature, coherentWidth]; ring
