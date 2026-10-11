-- Prove2me | solution 1 for BookProof.ChapterThermalTemperatureCore.norm_lt_one_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:33:56.895991+00:00
-- url     : https://prove2.me/submissions/3a8c6724-58fd-44a9-9154-0d5c8d9e9715

-- Generated from ChapterThermalTemperatureCore.lean — theorem BookProof.ChapterThermalTemperatureCore.norm_lt_one_of_lt_one
import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Mathlib
import Definitions.Def_ChapterThermalTemperatureCore
open BookProof.ChapterThermalTemperatureCore


noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {r : ℝ}
open BookProof.ChapterThermalTemperatureCore

theorem solution(h0 : 0 ≤ r) (h1 : r < 1) : ‖r‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1
