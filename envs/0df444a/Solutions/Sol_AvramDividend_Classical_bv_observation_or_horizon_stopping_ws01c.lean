-- Prove2me | solution 1 for AvramDividend.Classical.bv_observation_or_horizon_stopping_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:04:10.185125+00:00
-- url     : https://prove2.me/submissions/d29352ed-7585-4c64-87cc-bcfcbe2836db

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ)
    (g : Ω → ℝ) (t H : ℝ≥0) (htH : t ≤ H)
    (hg : Measurable[ℱ t] g) (b : ℝ) :
    IsStoppingTime ℱ
      (fun ω : Ω => ((if g ω < b then t else H : ℝ≥0) :
        WithTop ℝ≥0)) := by
  intro i
  have hS : MeasurableSet[ℱ t] {ω | g ω < b} := measurableSet_lt hg measurable_const
  by_cases hH : H ≤ i
  · convert @MeasurableSet.univ Ω (ℱ i)
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    split_ifs
    · exact_mod_cast le_trans htH hH
    · exact_mod_cast hH
  · by_cases ht : t ≤ i
    · convert ℱ.mono ht _ hS using 1
      ext ω
      simp only [Set.mem_setOf_eq]
      split_ifs with h
      · simp only [h, iff_true]; exact_mod_cast ht
      · simp only [h, iff_false]; exact_mod_cast hH
    · convert @MeasurableSet.empty Ω (ℱ i)
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      split_ifs
      · exact_mod_cast ht
      · exact_mod_cast hH
