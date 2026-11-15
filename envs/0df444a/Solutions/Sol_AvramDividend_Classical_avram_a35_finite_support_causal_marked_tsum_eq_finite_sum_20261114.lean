-- Prove2me | solution 1 for AvramDividend.Classical.avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:12:41.00321+00:00
-- url     : https://prove2.me/submissions/0bb84850-1eae-4de2-bac0-ac103ede0726

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (a : ℝ≥0 → ℝ) (T : ℝ≥0) (S : Finset ℝ≥0)
    (hS : ∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ a u ≠ 0) :
    ∀ t : ℝ≥0, t ≤ T →
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then a u else 0) =
        ∑ u ∈ S, if u ≤ t then a u else 0 := by
  classical
  intro t ht
  have hOut (u : ℝ≥0) (hu : u ∉ S) :
      (if 0 < u ∧ u ≤ t then a u else 0) = 0 := by
    by_cases hTime : 0 < u ∧ u ≤ t
    · have ha : a u = 0 := by
        by_contra hne
        exact hu ((hS u).mpr ⟨hTime.1, le_trans hTime.2 ht, hne⟩)
      simp [ha]
    · simp [hTime]
  calc
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then a u else 0) =
      ∑ u ∈ S, if 0 < u ∧ u ≤ t then a u else 0 :=
        tsum_eq_sum hOut
    _ = ∑ u ∈ S, if u ≤ t then a u else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have hpos : 0 < u := ((hS u).mp hu).1
      simp [hpos]
