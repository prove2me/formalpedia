-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_interarrival_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:51:55.605048+00:00
-- url     : https://prove2.me/submissions/3dd04143-a605-48d3-bcbd-0352f3903843

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section
/-- The original unit-rate compound-Poisson waits obey the exact exponential
    survival law, with no auxiliary probability space. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t < τ n ω} = ENNReal.ofReal (Real.exp (-t)) := by
  exact AvramDividend.Classical.chat06_unit_exponential_haslaw_survival
    (τ n) (hd.law_interarrival n) t ht