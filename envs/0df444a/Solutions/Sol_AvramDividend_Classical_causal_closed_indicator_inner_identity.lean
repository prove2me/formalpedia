-- Prove2me | solution 1 for AvramDividend.Classical.causal_closed_indicator_inner_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:59:29.74878+00:00
-- url     : https://prove2.me/submissions/b0bcf641-d8dd-4ddb-a6de-e887a00397cc

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K g : ℝ → ℝ) (t x : ℝ)
    (ht : 0 ≤ t) (htx : t ≤ x) :
    (∫ u in Ioc (0 : ℝ) t, K u * g (t - u) ∂volume) =
    (∫ u : ℝ,
      ((Ioi (0 : ℝ)).indicator K) u *
      ((Icc (0 : ℝ) x).indicator g) (t - u) ∂volume) := by
  rw [← integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  by_cases hu : 0 < u
  · have huIoi : u ∈ Ioi (0 : ℝ) := hu
    by_cases hut : u ≤ t
    · have huIoc : u ∈ Ioc (0 : ℝ) t := ⟨hu, hut⟩
      have hgi : t - u ∈ Icc (0 : ℝ) x := by
        constructor
        · exact sub_nonneg.mpr hut
        · linarith [htx, hu]
      simp only [Set.indicator_of_mem huIoc,
        Set.indicator_of_mem huIoi, Set.indicator_of_mem hgi]
    · have hnot : u ∉ Ioc (0 : ℝ) t := by
        intro hs
        exact hut hs.2
      have hnot2 : t - u ∉ Icc (0 : ℝ) x := by
        intro hs
        exact hut (sub_nonneg.mp hs.1)
      simp only [Set.indicator_of_notMem hnot,
        Set.indicator_of_mem huIoi, Set.indicator_of_notMem hnot2,
        mul_zero]
  · have hnot : u ∉ Ioc (0 : ℝ) t := by
      intro hs
      exact hu hs.1
    have hnot2 : u ∉ Ioi (0 : ℝ) := hu
    simp only [Set.indicator_of_notMem hnot,
      Set.indicator_of_notMem hnot2, zero_mul]
