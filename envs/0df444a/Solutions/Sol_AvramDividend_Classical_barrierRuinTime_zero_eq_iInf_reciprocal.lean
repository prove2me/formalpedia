-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_zero_eq_iInf_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:37:02.87524+00:00
-- url     : https://prove2.me/submissions/d01ed489-0fd4-4065-9610-def6b4913e80

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_eq_iInf_positive
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Countably many decreasing positive drawdown thresholds recover zero ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    barrierRuinTime X 0 ω =
      ⨅ n : ℕ, barrierRuinTime X (1 / ((n : ℝ) + 1)) ω := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    have hn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    exact barrierRuinTime_mono_barrier X 0
      (1 / ((n : ℝ) + 1)) hn ω
  · rw [barrierRuinTime_zero_eq_iInf_positive X ω]
    refine le_iInf fun ε => le_iInf fun hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact le_trans
      (iInf_le (fun k : ℕ =>
        barrierRuinTime X (1 / ((k : ℝ) + 1)) ω) n)
      (barrierRuinTime_mono_barrier X
        (1 / ((n : ℝ) + 1)) ε (le_of_lt hn) ω)
