-- Prove2me | solution 1 for BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:15:02.577554+00:00
-- url     : https://prove2.me/submissions/5578a4db-7933-42dd-842a-7e4476324f98

-- Generated from ChapterBaryonAsymmetry.lean — solution of BookProof.ChapterBaryonAsymmetry.matterRadiationRatio_eq
import Mathlib
import Definitions.Def_ChapterBaryonAsymmetry
open BookProof.ChapterBaryonAsymmetry













open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (ρm0 ρr0 a : ℝ) (ha : 0 < a) (hr : ρr0 ≠ 0) :
    matterRadiationRatio ρm0 ρr0 a = (ρm0 / ρr0) * a := by

  have hane : a ≠ 0 := ne_of_gt ha
  simp only [matterRadiationRatio, matterDensity, radDensity]
  field_simp
