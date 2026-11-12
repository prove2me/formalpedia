-- Prove2me | solution 1 for BunkbedAux.probOf_mem_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T03:46:52.524189+00:00
-- url     : https://prove2.me/submissions/f77f8a30-8572-4579-b1f3-e853edb2eb2c

import Theorems.Thm_BunkbedAux_sum_weight_eq_one
open Bunkbed Finset

/-- **Percolation probabilities lie in `[0,1]`.** -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (ev : Finset (Sym2 V) → Prop) [DecidablePred ev] :
    0 ≤ probOf E w ev ∧ probOf E w ev ≤ 1 := by
  have hwt : ∀ S : Finset (Sym2 V), 0 ≤ weight E w S := by
    intro S
    unfold weight
    exact mul_nonneg (Finset.prod_nonneg fun e _ => hw0 e)
      (Finset.prod_nonneg fun e _ => by linarith [hw1 e])
  constructor
  · unfold probOf
    refine Finset.sum_nonneg (fun S _ => ?_)
    split
    · exact hwt S
    · exact le_refl 0
  · have h1 : probOf E w ev ≤ ∑ S ∈ E.powerset, weight E w S := by
      unfold probOf
      refine Finset.sum_le_sum (fun S _ => ?_)
      split
      · exact le_refl _
      · exact hwt S
    rw [BunkbedAux.sum_weight_eq_one E w] at h1
    exact h1
