-- Prove2me | solution 1 for BookProof.ChapterG2.cond_of_null
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:20:34.803987+00:00
-- url     : https://prove2.me/submissions/f6a95278-6c23-4719-9a28-3b2874328aa8

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.cond_of_null
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure Ω) {C : Set Ω} (hC : μ C = 0) : μ[|C] = 0 := by

  simp [ ProbabilityTheory.cond, MeasureTheory.Measure.restrict_eq_zero.mpr hC ]
