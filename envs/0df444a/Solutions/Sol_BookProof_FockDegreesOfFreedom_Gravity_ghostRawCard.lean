-- Prove2me | solution 1 for BookProof.FockDegreesOfFreedom.Gravity.ghostRawCard
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:19:39.701589+00:00
-- url     : https://prove2.me/submissions/b918580a-d021-4b7c-867c-69e7557ed44f

import Mathlib
import Definitions.Def_ChapterFockDegreesOfFreedom
-- Generated from ChapterFockDegreesOfFreedom.lean — theorem BookProof.FockDegreesOfFreedom.Gravity.ghostRawCard
open BookProof.FockDegreesOfFreedom
open BookProof.FockDegreesOfFreedom.Gravity



open Fintype
theorem solution : ¬ (Fintype.card GhostRaw = 3 + 1) := by
  simp [GhostRaw]
