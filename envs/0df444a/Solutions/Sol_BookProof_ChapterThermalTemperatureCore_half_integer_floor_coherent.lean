-- Prove2me | solution 1 for BookProof.ChapterThermalTemperatureCore.half_integer_floor_coherent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:33:55.610635+00:00
-- url     : https://prove2.me/submissions/05280ed3-d240-4f40-9d89-f5ea933fb6cb

-- Generated from ChapterThermalTemperatureCore.lean — solution of BookProof.ChapterThermalTemperatureCore.half_integer_floor_coherent
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
import Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_energy
import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterBoseEinstein
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterThermalTemperatureCore



noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {r : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution {lam : ℝ} (h : 0 ≤ lam) :
    1 / 2 ≤ ∑' n : ℕ, ((n : ℝ) + 1 / 2) * coherentOccupation lam n := by

  rw [coherentOccupation_energy]
  linarith
