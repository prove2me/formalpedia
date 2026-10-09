-- Prove2me | solution 1 for BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_fidelity_width_sub_coherent_half
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:37:27.329187+00:00
-- url     : https://prove2.me/submissions/96a4e814-4965-45e9-9e82-28512f8f0ca2

-- Generated from ChapterCoherentThermalFidelity.lean — solution of BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_fidelity_width_sub_coherent_half
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
import Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_width_unique
open BookProof.ChapterCoherentThermalFidelity



noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

variable {nbar lam : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar)
    {w : ℝ} (hw : 0 < w)
    (hfid : ∀ lam : ℝ, coherentThermalFidelity nbar lam = Real.exp (-(lam / w)) / w) :
    thermalTemperature nbar = w - coherentWidth := by

  rw [width_unique h hw hfid, thermalTemperature, coherentWidth]
  ring
