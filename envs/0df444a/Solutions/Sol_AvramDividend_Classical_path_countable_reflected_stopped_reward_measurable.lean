-- Prove2me | solution 1 for AvramDividend.Classical.path_countable_reflected_stopped_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T10:17:36.678116+00:00
-- url     : https://prove2.me/submissions/f1e003a9-eedc-420b-bbf7-7f788323d735

import Theorems.Thm_AvramDividend_Classical_path_countable_killed_record_grid_reward_measurable
import Theorems.Thm_AvramDividend_Classical_path_countable_drawdown_ruin_clock_measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical

/-- The full countably sampled, killed reflected-dividend reward is path-Borel measurable. -/
theorem solution
    (samples : ℕ → ℝ≥0) (mesh : ℕ → ℕ → ℝ≥0)
    (weights : ℕ → ℕ → ℝ≥0∞) (a : ℝ) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
        if (mesh n (k + 1) : ℝ≥0∞) <
          (⨅ i : ℕ,
            if f (samples i) - f 0 -
              (⨆ j : ℕ,
                if samples j ≤ samples i then
                  ENNReal.ofReal (f (samples j) - f 0)
                else 0).toReal < -a then
              (samples i : ℝ≥0∞)
            else ⊤) then
          weights n k * ENNReal.ofReal
            ((⨆ i : ℕ,
                if samples i ≤ mesh n (k + 1) then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal -
              (⨆ i : ℕ,
                if samples i ≤ mesh n k then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal)
        else 0) := by
  classical
  have hstop : Measurable (fun f : ℝ≥0 → ℝ =>
      ⨅ i : ℕ,
        if f (samples i) - f 0 -
          (⨆ j : ℕ,
            if samples j ≤ samples i then
              ENNReal.ofReal (f (samples j) - f 0)
            else 0).toReal < -a then
          (samples i : ℝ≥0∞)
        else ⊤) :=
    AvramDividend.Classical.path_countable_drawdown_ruin_clock_measurable samples a
  apply Measurable.iSup
  intro n
  exact AvramDividend.Classical.path_countable_killed_record_grid_reward_measurable
    samples (mesh n) _ hstop (weights n)
