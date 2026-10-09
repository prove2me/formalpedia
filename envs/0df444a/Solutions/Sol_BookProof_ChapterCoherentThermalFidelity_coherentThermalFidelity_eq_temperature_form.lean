-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq_temperature_form
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:36:49.513983+00:00
-- url     : https://prove2.me/submissions/e322f668-71f7-4874-9dd8-e5d2f2a3b598

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq_temperature_form
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
import Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_eq
import Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_width_eq
open BookProof.ChapterCoherentThermalFidelity



noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

variable {nbar lam : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) (lam : ℝ) :
    coherentThermalFidelity nbar lam
      = Real.exp (-(lam / (thermalTemperature nbar + coherentWidth)))
        / (thermalTemperature nbar + coherentWidth) := by

  rw [coherentThermalFidelity_eq h, ← coherentThermalFidelity_width_eq]
