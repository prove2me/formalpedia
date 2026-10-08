-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_countable_positive_rightLimit_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:28:40.453479+00:00
-- url     : https://prove2.me/submissions/1c462e25-3930-4ade-b4c2-9195494744e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_countable_rightJump_times
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Set.Countable {t : ℝ |
      0 ≤ t ∧ rightLimit D t.toNNReal ω ≠ D t.toNNReal ω} := by
  have hCount :=
    dividendStrategy_countable_rightJump_times D hD ω
  refine hCount.mono ?_
  intro t ht
  obtain ⟨ht0, hjump⟩ := ht
  have heq : ((t.toNNReal : ℝ)) = t := Real.coe_toNNReal t ht0
  have hlim :=
    dividendPath_real_rightLim_eq_rightLimit
      D ω (hD.2.1 ω) t.toNNReal
  rw [heq] at hlim
  change Function.rightLim (fun s : ℝ => D s.toNNReal ω) t ≠
    D t.toNNReal ω
  rw [hlim]
  exact hjump
