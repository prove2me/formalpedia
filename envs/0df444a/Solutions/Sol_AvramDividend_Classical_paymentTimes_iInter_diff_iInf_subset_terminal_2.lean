-- Prove2me | solution 2 for AvramDividend.Classical.paymentTimes_iInter_diff_iInf_subset_terminal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:43:55.580681+00:00
-- url     : https://prove2.me/submissions/559c4030-e748-47ee-9907-e204f3dfabb8

import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (σ : ℕ → ℝ≥0∞) :
    (⋂ n, paymentTimes (σ n)) \
        paymentTimes (⨅ n, σ n) ⊆
      {t : ℝ | ENNReal.ofReal t = ⨅ n, σ n} := by
  rintro t ⟨ht, hnot⟩
  simp only [mem_iInter, paymentTimes, mem_setOf_eq] at ht hnot ⊢
  have h0 : 0 ≤ t := (ht 0).1
  have hne : t ≠ 0 := fun h => hnot ⟨h0, Or.inl h⟩
  have hlt : ∀ n, ENNReal.ofReal t < σ n := fun n => ((ht n).2.resolve_left hne)
  refine le_antisymm (le_iInf fun n => (hlt n).le) ?_
  exact not_lt.mp fun h => hnot ⟨h0, Or.inr h⟩
