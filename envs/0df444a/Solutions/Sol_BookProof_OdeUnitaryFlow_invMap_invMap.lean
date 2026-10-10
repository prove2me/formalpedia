-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.invMap_invMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:14.829833+00:00
-- url     : https://prove2.me/submissions/21d8f2f2-a6dc-4384-820d-e9bc6a2f6ce3

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.invMap_invMap
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {x : ℝ} (hx : x ≠ 0) : invMap (invMap x) = x := by

  simp only [invMap]
  field_simp
