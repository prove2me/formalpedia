-- Prove2me | solution 1 for AvramDividend.Classical.capped_untopA_stoppedHistory_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:55:26.056177+00:00
-- url     : https://prove2.me/submissions/4a812d10-25f3-4a55-874e-44ec70b1df83

import Mathlib.Probability.Process.Stopping
import Mathlib.Order.WithBot
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_stoppingTime_finite_cap_untopA_le_events
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_measurable_of_equal_finite_clocks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0∞}
    (hτ : IsStoppingTime 𝓕 τ) (N : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[(hτ.min_const N).measurableSpace] A) :
    MeasurableSet[
      (isStoppingTime_withTop_of_le_events
        (fun ω => (min (τ ω) (N : ℝ≥0∞)).untopA)
        (stoppingTime_finite_cap_untopA_le_events hτ N)).measurableSpace] A := by
  have hcast (ω : Ω) :
      (((min (τ ω) (N : ℝ≥0∞)).untopA : ℝ≥0) : ℝ≥0∞) =
        min (τ ω) (N : ℝ≥0∞) := by
    have hn : min (τ ω) (N : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
    calc
      ((min (τ ω) (N : ℝ≥0∞)).untopA : ℝ≥0∞) =
          ((min (τ ω) (N : ℝ≥0∞)).untop hn : ℝ≥0∞) :=
        congrArg (fun v : ℝ≥0 => (v : ℝ≥0∞))
          (WithTop.untopA_eq_untop hn)
      _ = _ := WithTop.coe_untop _ hn
  exact stoppedHistory_measurable_of_equal_finite_clocks
    (𝓕 := 𝓕)
    (fun ω => (min (τ ω) (N : ℝ≥0∞)).untopA)
    (stoppingTime_finite_cap_untopA_le_events hτ N)
    (fun ω => min (τ ω) (N : ℝ≥0∞))
    (hτ.min_const N) hcast A hA
