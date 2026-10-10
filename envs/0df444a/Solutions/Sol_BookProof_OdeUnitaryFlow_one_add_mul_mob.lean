-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.one_add_mul_mob
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:06.08931+00:00
-- url     : https://prove2.me/submissions/e881ed6e-c7b6-4a04-b9dc-e81e11674ba5

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.one_add_mul_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (s t x : ℝ) (hx : 1 + t * x ≠ 0) :
    1 + s * mob t x = (1 + (s + t) * x) / (1 + t * x) := by

  have hx' : 1 + x * t ≠ 0 := by rwa [mul_comm] at hx
  rw [mob, eq_div_iff hx]
  field_simp
  ring
