-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_disjoint_cell_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:19:02.974562+00:00
-- url     : https://prove2.me/submissions/f70de348-4919-4fb4-b11d-c82b77c5b2cc

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (μ : Measure ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, StrictMono (u n))
    (c : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (n0 : ℕ)
    (hc : ∀ n, n0 ≤ n → ∀ i ∈ Finset.range (n + 1), ‖c n i‖ ≤ C) :
    let G : ℕ → ℝ≥0 → ℝ := fun n t => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < t ∧ t ≤ u n (i + 1) then c n i else 0
      else 0
    (∀ n, AEStronglyMeasurable (G n) μ) ∧ (∀ n t, ‖G n t‖ ≤ C) := by
  intro G
  have hmeas (n : ℕ) : AEStronglyMeasurable (G n) μ := by
    apply Measurable.aestronglyMeasurable
    by_cases hn : n0 ≤ n
    · simp only [G, if_pos hn]
      apply Finset.measurable_sum
      intro i hi
      have hconst : Measurable (fun _ : ℝ≥0 => c n i) := measurable_const
      exact hconst.piecewise
        (measurableSet_Ioc (a := u n i) (b := u n (i + 1))) measurable_const
    · simpa only [G, if_neg hn] using
        (measurable_const : Measurable (fun _ : ℝ≥0 => (0 : ℝ)))
  refine ⟨hmeas, ?_⟩
  intro n t
  by_cases hn : n0 ≤ n
  · dsimp only [G]
    rw [if_pos hn]
    by_cases hex : ∃ i ∈ Finset.range (n + 1), u n i < t ∧ t ≤ u n (i + 1)
    · obtain ⟨i, hi, hic⟩ := hex
      rw [Finset.sum_eq_single i]
      · rw [if_pos hic]
        exact hc n hn i hi
      · intro j hj hji
        have hnot : ¬ (u n j < t ∧ t ≤ u n (j + 1)) := by
          intro hjc
          rcases lt_or_gt_of_ne hji with hji' | hij'
          · have hji'' : j + 1 ≤ i := by omega
            exact (not_lt_of_ge hjc.2) (((hu n).monotone hji'').trans_lt hic.1)
          · have hij'' : i + 1 ≤ j := by omega
            exact (not_lt_of_ge hic.2) (((hu n).monotone hij'').trans_lt hjc.1)
        exact if_neg hnot
      · intro hni
        exact False.elim (hni hi)
    · have hz : (∑ i ∈ Finset.range (n + 1),
          if u n i < t ∧ t ≤ u n (i + 1) then c n i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact if_neg (fun hic => hex ⟨i, hi, hic⟩)
      simpa only [hz, norm_zero] using hC
  · simpa only [G, if_neg hn, norm_zero] using hC
