-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_finite_true_negative_smallmark_total_amplitude_le_actual_jump_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:58:23.15986+00:00
-- url     : https://prove2.me/submissions/868a9cd4-b2c3-4a30-b401-4c1ff6b69b58

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {α : Type*} (S : Finset α) (z : α → ℝ) :
    ‖∑ u ∈ S, if -1 < z u ∧ z u < 0 then z u else 0‖ ≤
      (S.card : ℝ) := by
  classical
  have hOne (u : α) :
      ‖if -1 < z u ∧ z u < 0 then z u else 0‖ ≤ (1 : ℝ) := by
    by_cases hz : -1 < z u ∧ z u < 0
    · simp only [if_pos hz, Real.norm_eq_abs]
      rw [abs_of_nonpos (le_of_lt hz.2)]
      linarith [hz.1]
    · simp [hz]
  calc
    ‖∑ u ∈ S, if -1 < z u ∧ z u < 0 then z u else 0‖ ≤
        ∑ u ∈ S, ‖if -1 < z u ∧ z u < 0 then z u else 0‖ :=
      norm_sum_le S (fun u => if -1 < z u ∧ z u < 0 then z u else 0)
    _ ≤ ∑ _u ∈ S, (1 : ℝ) :=
      Finset.sum_le_sum (fun u _ => hOne u)
    _ = (S.card : ℝ) := by simp
