-- Prove2me | solution 1 for AvramDividend.Classical.stopped_lintegral_Ioc_partition_fin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:46:14.860082+00:00
-- url     : https://prove2.me/submissions/bee00f12-37d5-4059-a7a0-5dacc337cc7d

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_partition_fin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical
open AvramDividend.Classical

theorem solution
    (μ : Measure ℝ) (A : Set ℝ) (f : ℝ → ℝ≥0∞)
    (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    (∫⁻ r in A, if r ∈ Set.Ioc (u 0) (u n) then f r else 0 ∂μ) =
    ∑ i ∈ Finset.range n,
      ∫⁻ r in A,
        if r ∈ Set.Ioc (u i) (u (i + 1)) then f r else 0 ∂μ := by
  classical
  let ν : Measure ℝ := μ.restrict A
  have hr (a c : ℝ) :
      (∫⁻ r in A, if r ∈ Set.Ioc a c then f r else 0 ∂μ) =
      (∫⁻ r in Set.Ioc a c, f r ∂ν) := by
    change (∫⁻ r, if r ∈ Set.Ioc a c then f r else 0 ∂ν) = _
    have hf :
        (fun r : ℝ => if r ∈ Set.Ioc a c then f r else 0) =
          (Set.Ioc a c).indicator f := by
      funext r
      by_cases h : r ∈ Set.Ioc a c
      · simp [h, Set.indicator_of_mem h]
      · simp [h, Set.indicator_of_notMem h]
    rw [hf]
    exact lintegral_indicator measurableSet_Ioc f
  calc
    (∫⁻ r in A, if r ∈ Set.Ioc (u 0) (u n) then f r else 0 ∂μ) =
      (∫⁻ r in Set.Ioc (u 0) (u n), f r ∂ν) := hr _ _
    _ = ∑ i ∈ Finset.range n,
        ∫⁻ r in Set.Ioc (u i) (u (i + 1)), f r ∂ν :=
      lintegral_Ioc_partition_fin ν f u hu n
    _ = ∑ i ∈ Finset.range n,
        ∫⁻ r in A,
          if r ∈ Set.Ioc (u i) (u (i + 1)) then f r else 0 ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hr _ _).symm
