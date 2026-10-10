-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.mob_neg_eq_classicalSol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:56.523369+00:00
-- url     : https://prove2.me/submissions/a5ab6379-108e-45d6-9fb2-5aae3ca9d527

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.mob_neg_eq_classicalSol
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (x₀ t : ℝ) : mob (-t) x₀ = classicalSol x₀ t := by

  have h : 1 + (-t) * x₀ = 1 - t * x₀ := by ring
  rw [mob, classicalSol, h]
