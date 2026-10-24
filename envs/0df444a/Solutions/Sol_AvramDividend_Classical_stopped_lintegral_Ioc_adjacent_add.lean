-- Prove2me | solution 1 for AvramDividend.Classical.stopped_lintegral_Ioc_adjacent_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:41:45.148913+00:00
-- url     : https://prove2.me/submissions/98a429d3-bc1a-4826-a4a5-09d7d08d2842

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_adjacent_add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- The stopped payout of two consecutive half-open intervals is their
sum, including when the underlying Stieltjes measure has infinite mass. -/
theorem solution
    (μ : Measure ℝ) (A : Set ℝ) (f : ℝ → ℝ≥0∞)
    (s t u : ℝ) (hst : s ≤ t) (htu : t ≤ u) :
    (∫⁻ r in A, if r ∈ Set.Ioc s u then f r else 0 ∂μ) =
      (∫⁻ r in A, if r ∈ Set.Ioc s t then f r else 0 ∂μ) +
      (∫⁻ r in A, if r ∈ Set.Ioc t u then f r else 0 ∂μ) := by
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
    (∫⁻ r in A, if r ∈ Set.Ioc s u then f r else 0 ∂μ) =
      (∫⁻ r in Set.Ioc s u, f r ∂ν) := hr s u
    _ = (∫⁻ r in Set.Ioc s t, f r ∂ν) +
        (∫⁻ r in Set.Ioc t u, f r ∂ν) :=
      lintegral_Ioc_adjacent_add ν f s t u hst htu
    _ = (∫⁻ r in A, if r ∈ Set.Ioc s t then f r else 0 ∂μ) +
        (∫⁻ r in A, if r ∈ Set.Ioc t u then f r else 0 ∂μ) := by
      rw [hr s t, hr t u]
