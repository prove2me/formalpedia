-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a25_finite_sum_positive_part_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:26:35.310514+00:00
-- url     : https://prove2.me/submissions/440cb4ac-0693-4fe3-b227-b44073244108

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) :
    max (∑ i ∈ s, a i) 0 ≤ ∑ i ∈ s, max (a i) 0 := by
  have hsum : (∑ i ∈ s, a i) ≤ ∑ i ∈ s, max (a i) 0 := by
    exact Finset.sum_le_sum (fun i hi => le_max_left (a i) 0)
  have hnon : (0 : ℝ) ≤ ∑ i ∈ s, max (a i) 0 := by
    exact Finset.sum_nonneg (fun i hi => le_max_right (a i) 0)
  exact max_le hsum hnon
