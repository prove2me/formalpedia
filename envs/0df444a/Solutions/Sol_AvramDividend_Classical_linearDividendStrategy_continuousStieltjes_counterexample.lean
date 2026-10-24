-- Prove2me | solution 1 for AvramDividend.Classical.linearDividendStrategy_continuousStieltjes_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:54:04.122954+00:00
-- url     : https://prove2.me/submissions/39d3121c-13a9-48e4-abfa-f0bab55fef76

import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

local instance : MeasurableSpace Unit := ⊤

theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0 (⊤ : MeasurableSpace Unit)),
      IsDividendStrategy 𝓕 (fun t (_ : Unit) => (t : ℝ)) ∧
      (∀ t : ℝ≥0, rightLimit (fun s (_ : Unit) => (s : ℝ)) t () = (t : ℝ)) ∧
      dividendMeasure (fun t (_ : Unit) => (t : ℝ)) ()
        (Ico (0 : ℝ) 1) = (1 : ENNReal) := by
  have hmono : Monotone (fun t : ℝ≥0 => (t : ℝ)) := by
    intro a b hab
    exact_mod_cast hab
  have hcont : Continuous (fun t : ℝ≥0 => (t : ℝ)) := by
    fun_prop
  have hstrategy :
      IsDividendStrategy (⊤ : Filtration ℝ≥0 (⊤ : MeasurableSpace Unit))
        (fun t (_ : Unit) => (t : ℝ)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ω
      simp
    · intro ω
      exact hmono
    · intro ω t
      exact hcont.continuousWithinAt
    · intro t
      exact measurable_const
  refine ⟨⊤, hstrategy, ?_, ?_⟩
  · intro t
    exact rightLimit_eq_of_monotone_right_continuous
      (fun s (_ : Unit) => (s : ℝ)) () t hmono
      hcont.continuousWithinAt
  · simpa using dividendMeasure_Ico_zero_eq_dividendValue
      (fun t (_ : Unit) => (t : ℝ)) hstrategy () (1 : ℝ≥0)
