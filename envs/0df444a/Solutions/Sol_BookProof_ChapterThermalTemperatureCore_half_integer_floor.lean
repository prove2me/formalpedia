-- Prove2me | solution 1 for BookProof.ChapterThermalTemperatureCore.half_integer_floor
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:33:54.005571+00:00
-- url     : https://prove2.me/submissions/1edb3c42-da45-4452-86f2-c021e27cae86

-- Generated from ChapterThermalTemperatureCore.lean — solution of BookProof.ChapterThermalTemperatureCore.half_integer_floor
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
import Theorems.Thm_BookProof_ChapterCoherentOccupation_thermalOccupation_energy
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterThermalTemperatureCore



noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {r : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {nbar : ℝ} (h : 0 ≤ nbar) :
    1 / 2 ≤ (∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n) ∧
      ((∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n) = 1 / 2 ↔ nbar = 0) := by

  rw [thermalOccupation_energy h]
  constructor
  · linarith
  · constructor
    · intro hEq; linarith
    · intro hEq; rw [hEq]; ring
