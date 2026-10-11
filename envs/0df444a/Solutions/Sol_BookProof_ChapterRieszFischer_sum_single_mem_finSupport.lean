-- Prove2me | solution 1 for BookProof.ChapterRieszFischer.sum_single_mem_finSupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:52:41.403378+00:00
-- url     : https://prove2.me/submissions/6bf555d4-c53c-4995-a975-77daf56d28ff

-- Generated from ChapterRieszFischer.lean — solution of BookProof.ChapterRieszFischer.sum_single_mem_finSupport
import Mathlib
import Definitions.Def_ChapterRieszFischer
open BookProof.ChapterRieszFischer



open Filter
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (f : Ell2) (s : Finset ℕ) :
    (∑ i ∈ s, lp.single 2 i ((f : ℕ → ℝ) i)) ∈ FinSupport := by

  refine Set.Finite.subset s.finite_toSet ?_
  intro j hj
  by_contra hjs
  apply hj
  simp only []
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hij : i ≠ j := by rintro rfl; exact hjs hi
  simp [hij]
