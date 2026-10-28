-- Prove2me | solution 1 for AvramDividend.Classical.path_countable_killed_record_grid_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:45:49.572632+00:00
-- url     : https://prove2.me/submissions/a4cd41cf-0b85-4bfe-9e6e-94c4b04799d7

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical

/-- A countable path-record grid reward with a measurable killing clock is measurable. -/
theorem solution
    (samples mesh : ℕ → ℝ≥0)
    (stop : (ℝ≥0 → ℝ) → ℝ≥0∞) (hstop : Measurable stop)
    (weights : ℕ → ℝ≥0∞) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ⨆ N : ℕ, ∑ k ∈ Finset.range N,
        if (mesh (k + 1) : ℝ≥0∞) < stop f then
          weights k * ENNReal.ofReal
            ((⨆ i : ℕ,
                if samples i ≤ mesh (k + 1) then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal -
              (⨆ i : ℕ,
                if samples i ≤ mesh k then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal)
        else 0) := by
  classical
  have hrecord (t : ℝ≥0) :
      Measurable (fun f : ℝ≥0 → ℝ =>
        (⨆ i : ℕ,
          if samples i ≤ t then
            ENNReal.ofReal (f (samples i) - f 0)
          else 0).toReal) := by
    apply Measurable.ennreal_toReal
    apply Measurable.iSup
    intro i
    by_cases hi : samples i ≤ t
    · simpa only [if_pos hi, Function.comp_def] using
        (ENNReal.measurable_ofReal.comp
          ((measurable_pi_apply (samples i)).sub
            (measurable_pi_apply (0 : ℝ≥0))))
    · simpa only [if_neg hi] using
        (measurable_const :
          Measurable (fun _ : ℝ≥0 → ℝ => (0 : ℝ≥0∞)))
  apply Measurable.iSup
  intro N
  apply Finset.measurable_sum
  intro k hk
  have hdiff : Measurable (fun f : ℝ≥0 → ℝ =>
        (⨆ i : ℕ,
          if samples i ≤ mesh (k + 1) then
            ENNReal.ofReal (f (samples i) - f 0)
          else 0).toReal -
        (⨆ i : ℕ,
          if samples i ≤ mesh k then
            ENNReal.ofReal (f (samples i) - f 0)
          else 0).toReal) :=
    (hrecord (mesh (k + 1))).sub (hrecord (mesh k))
  exact Measurable.ite (measurableSet_lt measurable_const hstop)
    (measurable_const.mul (ENNReal.measurable_ofReal.comp hdiff))
    measurable_const
