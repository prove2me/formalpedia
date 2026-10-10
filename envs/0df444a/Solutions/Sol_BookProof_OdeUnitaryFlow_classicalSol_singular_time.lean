-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.classicalSol_singular_time
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:55.345623+00:00
-- url     : https://prove2.me/submissions/4f78ef6c-d2ef-4dad-8b05-ccc130989119

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.classicalSol_singular_time
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (x₀ : ℝ) (hx₀ : x₀ ≠ 0) : 1 - (1 / x₀) * x₀ = 0 := by

  rw [one_div, inv_mul_cancel₀ hx₀, sub_self]
