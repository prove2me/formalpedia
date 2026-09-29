-- Prove2me | solution 1 for AvgCompletionSched.ParallelRelease.release_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T06:23:55.363391+00:00
-- url     : https://prove2.me/submissions/5aae8731-23ec-4b79-bb18-9fcf8b3f7f8f

import Mathlib
import Definitions.Def_AvgCompletionSched_ParallelRelease_Model

open AvgCompletionSched.ParallelRelease

theorem solution {n m : ℕ} (I : Instance n m) (Nstar : Schedule I) (α : ℝ)
    (hα : α * ∑ j, Nstar.C j < ∑ j, I.p j) :
    ∑ j, I.r j ≤ (1 - α) * ∑ j, Nstar.C j := by
  have h1 : ∑ j, (I.r j + I.p j) ≤ ∑ j, Nstar.C j := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Schedule.C]
    have := Nstar.released j
    linarith
  rw [Finset.sum_add_distrib] at h1
  linarith
