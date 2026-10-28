-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_iInter_diff_iInf_subset_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:43:44.133403+00:00
-- url     : https://prove2.me/submissions/ae97eba2-e0a5-444d-8758-01724b43271e

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Only the limiting terminal time can survive every pre-ruin payment window. -/
theorem solution (σ : ℕ → ℝ≥0∞) :
    (⋂ n, paymentTimes (σ n)) \
        paymentTimes (⨅ n, σ n) ⊆
      {t : ℝ | ENNReal.ofReal t = ⨅ n, σ n} := by
  intro t ht
  rcases ht with ⟨htall, hnot⟩
  have ht0 : 0 ≤ t := by
    have hfirst : t ∈ paymentTimes (σ 0) :=
      (Set.mem_iInter.mp htall) 0
    exact hfirst.1
  have hne : t ≠ 0 := by
    intro hzero
    apply hnot
    exact ⟨ht0, Or.inl hzero⟩
  have hle : ENNReal.ofReal t ≤ ⨅ n, σ n := by
    refine le_iInf fun n => ?_
    have hn : t ∈ paymentTimes (σ n) :=
      (Set.mem_iInter.mp htall) n
    rcases hn.2 with hz | hlt
    · exact (hne hz).elim
    · exact le_of_lt hlt
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact (hnot ⟨ht0, Or.inr hlt⟩).elim
  · exact heq
