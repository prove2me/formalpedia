-- Prove2me | solution 1 for BookProof.ProbabilityClockStochastic.Mab_isColumnStochastic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:38.637987+00:00
-- url     : https://prove2.me/submissions/96b3457f-af91-46e2-8b2c-7d43df2820a6

-- Generated from ChapterProbabilityClockStochastic.lean — solution of BookProof.ProbabilityClockStochastic.Mab_isColumnStochastic
import Mathlib
import Definitions.Def_ChapterProbabilityClockStochastic
open BookProof.ProbabilityClockStochastic




open Matrix
open scoped Norms.Operator

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) : IsColumnStochastic (Mab a b) := by

  refine ⟨?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp only [Mab, Fin.zero_eta, Fin.isValue, of_apply,
      cons_val', cons_val_zero, cons_val_fin_one, Fin.mk_one, cons_val_one] <;> positivity
  · intro j; fin_cases j <;>
      simp [Mab, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
