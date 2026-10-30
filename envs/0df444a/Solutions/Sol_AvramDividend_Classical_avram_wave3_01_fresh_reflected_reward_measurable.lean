-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_fresh_reflected_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:52:39.805275+00:00
-- url     : https://prove2.me/submissions/4cca2970-3037-47b3-b20e-d6be77964e06

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical

/-- The actual prospective upcrossing discount killed by a reflected
    drawdown, encoded on a countable time schedule, is path-Borel. -/
theorem solution
    (samples : ℕ → ℝ≥0) (a b q : ℝ) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      let ρ : ℝ≥0∞ := ⨅ i : ℕ,
        if b < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
      let σ : ℝ≥0∞ := ⨅ i : ℕ,
        if f (samples i) - f 0 -
          (⨆ j : ℕ,
            if samples j ≤ samples i then
              ENNReal.ofReal (f (samples j) - f 0)
            else 0).toReal < -a then
          (samples i : ℝ≥0∞) else ⊤
      if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
      else 0) := by
  classical
  let ρ : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
    ⨅ i : ℕ, if b < f (samples i) - f 0 then
      (samples i : ℝ≥0∞) else ⊤
  let σ : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
    ⨅ i : ℕ, if f (samples i) - f 0 -
      (⨆ j : ℕ, if samples j ≤ samples i then
        ENNReal.ofReal (f (samples j) - f 0)
      else 0).toReal < -a then
      (samples i : ℝ≥0∞) else ⊤
  have hρ : Measurable ρ := by
    dsimp only [ρ]
    apply Measurable.iInf
    intro i
    exact Measurable.ite
      (measurableSet_lt measurable_const
        ((measurable_pi_apply (samples i)).sub
          (measurable_pi_apply (0 : ℝ≥0))))
      measurable_const measurable_const
  have hrecord (t : ℝ≥0) : Measurable (fun f : ℝ≥0 → ℝ =>
      (⨆ j : ℕ, if samples j ≤ t then
        ENNReal.ofReal (f (samples j) - f 0) else 0).toReal) := by
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
  have hσ : Measurable σ := by
    dsimp only [σ]
    apply Measurable.iInf
    intro i
    have hdiff : Measurable (fun f : ℝ≥0 → ℝ =>
        f (samples i) - f 0 -
          (⨆ j : ℕ, if samples j ≤ samples i then
            ENNReal.ofReal (f (samples j) - f 0) else 0).toReal) :=
      ((measurable_pi_apply (samples i)).sub
        (measurable_pi_apply (0 : ℝ≥0))).sub
          (hrecord (samples i))
    exact Measurable.ite (measurableSet_lt hdiff measurable_const)
      measurable_const measurable_const
  change Measurable (fun f : ℝ≥0 → ℝ =>
    if ρ f < σ f then ENNReal.ofReal (Real.exp (-(q * (ρ f).toReal)))
    else 0)
  refine Measurable.ite (measurableSet_lt hρ hσ) ?_ measurable_const
  exact ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp
      ((measurable_const.mul (ENNReal.measurable_toReal.comp hρ)).neg))
