-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_mean_add_coherentWidth
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:37:41.040073+00:00
-- url     : https://prove2.me/submissions/e6506cf8-ce80-4ce9-a476-909f9f95bd00

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_mean_add_coherentWidth
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
    thermalTemperature nbar = nbar + coherentWidth := by

  rw [thermalTemperature, coherentWidth]
