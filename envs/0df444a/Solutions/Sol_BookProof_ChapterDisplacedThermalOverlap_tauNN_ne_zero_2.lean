-- Prove2me | solution 2 for BookProof.ChapterDisplacedThermalOverlap.tauNN_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:28:17.903701+00:00
-- url     : https://prove2.me/submissions/3ac3a51f-175a-48d8-9ef2-12992644d193

import Mathlib
import Definitions.Def_ChapterDisplacedThermalOverlap

open BookProof.ChapterDisplacedThermalOverlap
open scoped NNReal

theorem solution (nbar : ℝ≥0) : tauNN nbar ≠ 0 := by
  unfold tauNN
  apply ne_of_gt
  positivity
