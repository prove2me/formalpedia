-- Prove2me | solution 1 for AvramDividend.Classical.path_countable_drawdown_ruin_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:45:53.766901+00:00
-- url     : https://prove2.me/submissions/ec75e126-50a1-488c-98ef-741da1061830

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical

/-- The countable strict reflected-drawdown exit time is path-Borel measurable. -/
theorem solution
    (samples : ℕ → ℝ≥0) (a : ℝ) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ⨅ i : ℕ,
        if f (samples i) - f 0 -
          (⨆ j : ℕ,
            if samples j ≤ samples i then
              ENNReal.ofReal (f (samples j) - f 0)
            else 0).toReal < -a then
          (samples i : ℝ≥0∞)
        else ⊤) := by
  classical
  have hrecord (t : ℝ≥0) :
      Measurable (fun f : ℝ≥0 → ℝ =>
        (⨆ j : ℕ,
          if samples j ≤ t then
            ENNReal.ofReal (f (samples j) - f 0)
          else 0).toReal) := by
    apply Measurable.ennreal_toReal
    apply Measurable.iSup
    intro j
    by_cases hj : samples j ≤ t
    · simpa only [if_pos hj, Function.comp_def] using
        (ENNReal.measurable_ofReal.comp
          ((measurable_pi_apply (samples j)).sub
            (measurable_pi_apply (0 : ℝ≥0))))
    · simpa only [if_neg hj] using
        (measurable_const :
          Measurable (fun _ : ℝ≥0 → ℝ => (0 : ℝ≥0∞)))
  apply Measurable.iInf
  intro i
  have hdiff : Measurable (fun f : ℝ≥0 → ℝ =>
      f (samples i) - f 0 -
        (⨆ j : ℕ,
          if samples j ≤ samples i then
            ENNReal.ofReal (f (samples j) - f 0)
          else 0).toReal) :=
    ((measurable_pi_apply (samples i)).sub
      (measurable_pi_apply (0 : ℝ≥0))).sub
        (hrecord (samples i))
  exact Measurable.ite (measurableSet_lt hdiff measurable_const)
    measurable_const measurable_const
