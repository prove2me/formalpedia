-- Prove2me | solution 1 for BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_energy_expectation_coth
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:33:58.35552+00:00
-- url     : https://prove2.me/submissions/714fa813-22c2-401d-af42-33a192d0c4e5

-- Generated from ChapterThermalTemperatureCore.lean — solution of BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_energy_expectation_coth
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
import Theorems.Thm_BookProof_ChapterBoseEinstein_boseEinstein_pos
import Theorems.Thm_BookProof_ChapterBoseEinstein_thermalTemperature_boseEinstein_eq_coth
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
theorem solution {x : ℝ} (hx : 0 < x) :
    Real.cosh (x / 2) / (2 * Real.sinh (x / 2))
      = ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb (boseEinstein x) n := by

  rw [thermalOccupation_energy (le_of_lt (boseEinstein_pos hx)),
    ← thermalTemperature_boseEinstein_eq_coth hx, thermalTemperature]
