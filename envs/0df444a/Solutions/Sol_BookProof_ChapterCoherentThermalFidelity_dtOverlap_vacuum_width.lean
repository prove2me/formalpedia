-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.dtOverlap_vacuum_width
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:38:20.003763+00:00
-- url     : https://prove2.me/submissions/66edb483-7dd4-4774-a5e2-475fb1c8fd1a

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.dtOverlap_vacuum_width
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
    ((0 : NNReal) : ℝ) + 1 / 2 + (((0 : NNReal) : ℝ) + 1 / 2) = coherentWidth + coherentWidth := by

  rw [coherentWidth]
  norm_num
