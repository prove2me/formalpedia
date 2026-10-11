-- Prove2me | solution 1 for BookProof.ChapterThermalTemperatureCore.geometricOccupancy_eq_thermalProb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:28.87356+00:00
-- url     : https://prove2.me/submissions/79a04ea2-33af-4982-b754-d147be429da0

-- Generated from ChapterThermalTemperatureCore.lean — solution of BookProof.ChapterThermalTemperatureCore.geometricOccupancy_eq_thermalProb
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterThermalTemperatureCore



noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {r : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    geometricOccupancy r n = thermalProb (geometricMean r) n := by

  have h1' : (0 : ℝ) < 1 - r := by linarith
  have hratio : thermalRatio (geometricMean r) = r := by
    rw [thermalRatio, geometricMean]
    field_simp
    ring
  rw [thermalProb, hratio, geometricOccupancy, geometricMean]
  congr 1
  field_simp
  ring
