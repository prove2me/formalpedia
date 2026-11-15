-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_true_finite_smallnegative_mark_step_increment_le_interval_actual_jump_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:41:56.13333+00:00
-- url     : https://prove2.me/submissions/e1a7d15d-5e4d-4203-bc1d-481223cfa22e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ‖(∑ u ∈ S,
         if u ≤ t then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
      (∑ u ∈ S,
         if u ≤ s then (if -1 < z u ∧ z u < 0 then z u else 0) else 0)‖ ≤
      ((S.filter (fun u => s < u ∧ u ≤ t ∧ -1 < z u ∧ z u < 0)).card : ℝ)
    := by
  classical
  let f : ℝ≥0 → ℝ := fun u => if -1 < z u ∧ z u < 0 then z u else 0
  have hCell (u : ℝ≥0) :
      (if u ≤ t then f u else 0) - (if u ≤ s then f u else 0) =
      if s < u ∧ u ≤ t then f u else 0 := by
    by_cases hus : u ≤ s
    · have hut : u ≤ t := le_trans hus hst
      have hns : ¬ s < u := not_lt.mpr hus
      simp [hus, hut, hns]
    · by_cases hut : u ≤ t
      · have hsu : s < u := lt_of_not_ge hus
        simp [hus, hut, hsu]
      · simp [hus, hut]
  have hSum :
      (∑ u ∈ S, if u ≤ t then f u else 0) -
        (∑ u ∈ S, if u ≤ s then f u else 0) =
      ∑ u ∈ S, if s < u ∧ u ≤ t then f u else 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun u hu => hCell u)
  have hOne (u : ℝ≥0) :
      ‖if s < u ∧ u ≤ t then f u else 0‖ ≤
      if s < u ∧ u ≤ t ∧ -1 < z u ∧ z u < 0 then (1 : ℝ) else 0 := by
    by_cases hc : s < u ∧ u ≤ t
    · by_cases hz : -1 < z u ∧ z u < 0
      · have hAll : s < u ∧ u ≤ t ∧ -1 < z u ∧ z u < 0 :=
          ⟨hc.1, hc.2, hz.1, hz.2⟩
        simp only [f, if_pos hc, if_pos hz, if_pos hAll, Real.norm_eq_abs]
        rw [abs_of_nonpos (le_of_lt hz.2)]
        linarith [hz.1]
      · have hn : ¬ (s < u ∧ u ≤ t ∧ -1 < z u ∧ z u < 0) := by
          intro h; exact hz ⟨h.2.2.1, h.2.2.2⟩
        simp [f, hc, hz, hn]
    · have hn : ¬ (s < u ∧ u ≤ t ∧ -1 < z u ∧ z u < 0) := by
        intro h; exact hc ⟨h.1, h.2.1⟩
      simp [hc, hn]
  calc
    ‖(∑ u ∈ S, if u ≤ t then f u else 0) -
      (∑ u ∈ S, if u ≤ s then f u else 0)‖ =
      ‖∑ u ∈ S, if s < u ∧ u ≤ t then f u else 0‖ := by rw [hSum]
    _ ≤ ∑ u ∈ S, ‖if s < u ∧ u ≤ t then f u else 0‖ :=
      norm_sum_le S _
    _ ≤ ∑ u ∈ S,
        if s < u ∧ u ≤ t ∧ -1 < z u ∧ z u < 0 then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun u hu => hOne u)
    _ = ((S.filter (fun u => s < u ∧ u ≤ t ∧ -1 < z u ∧ z u < 0)).card : ℝ) := by simp
