-- Prove2me | solution 1 for BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_mean_half
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:33:57.001926+00:00
-- url     : https://prove2.me/submissions/d134fe69-a350-43fb-a13f-a4825aba3fef

-- Generated from ChapterThermalTemperatureCore.lean — solution of BookProof.ChapterThermalTemperatureCore.thermal_temperature_eq_mean_half
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
import Theorems.Thm_BookProof_ChapterBoseEinstein_boseEinstein_mean
import Theorems.Thm_BookProof_ChapterBoseEinstein_thermalTemperature_boseEinstein_eq_coth
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
      = (∑' n : ℕ, (n : ℝ) * thermalProb (boseEinstein x) n) + 1 / 2 := by

  rw [← thermalTemperature_boseEinstein_eq_coth hx, boseEinstein_mean hx, thermalTemperature]
