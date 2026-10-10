-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.hasDerivAt_mob
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:10.840508+00:00
-- url     : https://prove2.me/submissions/ffabe57b-89eb-4e93-9ca7-ae04cc504f08

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.hasDerivAt_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t x : ℝ) (hx : x ∈ flowDom t) :
    HasDerivAt (mob t) ((1 + t * x) ^ 2)⁻¹ x := by

  have h : 1 + t * x ≠ 0 := hx
  have hden : HasDerivAt (fun x : ℝ => 1 + t * x) t x := by
    simpa using ((hasDerivAt_id x).const_mul t).const_add 1
  have hq := (hasDerivAt_id x).div hden h
  have heq : (1 * (1 + t * x) - x * t) / (1 + t * x) ^ 2 = ((1 + t * x) ^ 2)⁻¹ := by
    field_simp
    ring
  simp only [mob, Pi.div_def, id_eq, heq] at hq
  exact hq
