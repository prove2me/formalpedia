-- Prove2me | solution 1 for BookProof.ChapterDisplacedThermalOverlap.tauNN_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:57:21.464989+00:00
-- url     : https://prove2.me/submissions/ca906dd1-7bdd-49bb-abc5-78752e425f0e

-- Generated from ChapterDisplacedThermalOverlap.lean — solution of BookProof.ChapterDisplacedThermalOverlap.tauNN_ne_zero
import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap
import Theorems.Thm_BookProof_ChapterDisplacedThermalOverlap_tauNN_pos
open BookProof.ChapterDisplacedThermalOverlap



noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option maxHeartbeats 1000000 in
theorem solution (nbar : ℝ≥0) : tauNN nbar ≠ 0 := by

  intro h
  have := tauNN_pos nbar
  rw [h] at this
  simp at this
