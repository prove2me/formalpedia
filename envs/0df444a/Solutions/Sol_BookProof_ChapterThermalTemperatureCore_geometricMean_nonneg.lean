-- Prove2me | solution 1 for BookProof.ChapterThermalTemperatureCore.geometricMean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:27.49655+00:00
-- url     : https://prove2.me/submissions/3bb20f5c-3e90-4087-ac42-6865ff17aecb

-- Generated from ChapterThermalTemperatureCore.lean — solution of BookProof.ChapterThermalTemperatureCore.geometricMean_nonneg
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
open BookProof.ChapterThermalTemperatureCore



noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {r : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h0 : 0 ≤ r) (h1 : r < 1) : 0 ≤ geometricMean r := div_nonneg h0 (by linarith)
