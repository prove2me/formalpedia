-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:54.068836+00:00
-- url     : https://prove2.me/submissions/f5685888-5e0b-4756-8d38-ccf9e66e26f3

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (x₀ t : ℝ) (ht : 1 - t * x₀ ≠ 0) :
    HasDerivAt (classicalSol x₀) ((classicalSol x₀ t) ^ 2) t := by

  have hnum : HasDerivAt (fun t : ℝ => 1 - t * x₀) (-x₀) t := by
    simpa using ((hasDerivAt_id t).mul_const x₀).const_sub 1
  have h := (hasDerivAt_const t x₀).div hnum ht
  have heq : (0 * (1 - t * x₀) - x₀ * -x₀) / (1 - t * x₀) ^ 2 = (classicalSol x₀ t) ^ 2 := by
    simp only [classicalSol, div_pow]
    ring
  simp only [classicalSol, Pi.div_def, heq] at h ⊢
  exact h
