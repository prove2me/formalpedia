-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.mob_mem_flowDom_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:03.241921+00:00
-- url     : https://prove2.me/submissions/1f350b44-cd27-4792-8e49-4d2faf9ae255

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.mob_mem_flowDom_neg
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_one_add_neg_mul_mob
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t x : ℝ) (hx : x ∈ flowDom t) : mob t x ∈ flowDom (-t) := by

  have h : 1 + t * x ≠ 0 := hx
  change 1 + (-t) * mob t x ≠ 0
  rw [one_add_neg_mul_mob t x hx]
  exact inv_ne_zero h
