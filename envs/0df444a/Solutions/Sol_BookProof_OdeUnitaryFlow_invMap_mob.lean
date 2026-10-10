-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.invMap_mob
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:16.413112+00:00
-- url     : https://prove2.me/submissions/f9ade277-c62a-47fb-b9db-68da65124152

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.invMap_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {t x : ℝ} (hx : x ≠ 0) :
    invMap (mob t x) = invMap x - t := by

  simp only [invMap, mob]
  field_simp
  ring
