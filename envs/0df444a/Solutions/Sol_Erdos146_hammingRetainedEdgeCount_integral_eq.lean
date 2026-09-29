-- Prove2me | solution 1 for Erdos146.hammingRetainedEdgeCount_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:37:58.081366+00:00
-- url     : https://prove2.me/submissions/b4c2fec6-f8f3-4783-8dc9-f55652d1dad2

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integrable
import Theorems.Thm_Erdos146_hammingRetentionMeasure_integral_eq_sum
import Theorems.Thm_Erdos146_hammingRetentionMeasure_real_event_eq_sum

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeCount dimension radius := by
  classical
  unfold hammingRetainedEdgeCount hammingExpectedRetainedEdgeCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun left _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ right : HammingWord dimension,
          if hammingDist left right ≤ radius ∧
              (false, left) ∈ retained ∧ (true, right) ∈ retained
          then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro left _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun right _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro right _
  by_cases hedge : hammingDist left right ≤ radius
  · simp only [hedge, true_and, if_true]
    rw [hammingRetentionMeasure_integral_eq_sum,
      hammingRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, left) ∈ retained ∧ (true, right) ∈ retained <;>
      simp [hretained]
  · simp [hedge]
