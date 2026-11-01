-- Prove2me | solution 1 for BudgetAgg.NashChar.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:50:36.952219+00:00
-- url     : https://prove2.me/submissions/6408e63f-39e3-40ad-b723-b71dd050404f

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_lemma_6

open BudgetAgg.NashChar

theorem solution {n m : ℕ} [NeZero n] [NeZero m]
    (Ps P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hnash : IsNashOutcome Ps q.1)
    (hcrit : ∀ i, crit (Ps i) q.1 = crit (P i) q.1) :
    IsNashOutcome P q.1 := by
  obtain ⟨s, hs, hsupp⟩ := (lemma_6 Ps q).1 hnash
  refine (lemma_6 P q).2 ⟨s, hs, ?_⟩
  intro i j hj
  exact hsupp i j (by rw [hcrit i]; exact hj)

