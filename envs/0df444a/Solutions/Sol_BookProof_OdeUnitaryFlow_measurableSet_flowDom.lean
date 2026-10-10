-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.measurableSet_flowDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:57.751164+00:00
-- url     : https://prove2.me/submissions/97324eb3-cf08-4028-9a32-3c5a1f961491

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.measurableSet_flowDom
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) : MeasurableSet (flowDom t) := by

  have hc : Continuous fun x : ℝ => 1 + t * x := by fun_prop
  have hset : flowDom t = ((fun x : ℝ => 1 + t * x) ⁻¹' {0})ᶜ := by
    ext x; simp [flowDom]
  rw [hset]
  exact ((measurableSet_singleton (0 : ℝ)).preimage hc.measurable).compl
